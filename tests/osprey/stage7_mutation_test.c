/*
 * OSPREY Stage 7.1, 7.3, and 7.4 focused tests: baseline access identity,
 * immutable mutation-plan ownership, and typed pointer application.
 *
 * Three layers:
 *
 *  - Locator capture matrix (drives the OSPREY runtime catalogs
 *    directly through the public hooks and checks
 *    osprey_capture_address_ref/osprey_capture_chunk_ref identity
 *    contracts: global/heap/stack cell locators, recursive stack
 *    activations, two live same-site heaps, numeric heap-base reuse
 *    across provenance generations, pointer target locator, NULL
 *    target, stale/freed rejection, and the interval rejection
 *    matrix).  Order-sensitive identity cases run under two actual
 *    insertion orders and check the distinctness rules that would fail
 *    if identity were reduced to raw address, canonical region alone,
 *    or site alone.
 *
 *  - Record-level groups: this translation unit includes
 *    linux-user/snapshot.c, which makes the child-side record writers
 *    and the parent-side analyze_collected_data() reachable (their
 *    state is static in snapshot.c).  snapshot.c also provides
 *    log_msg/trace_mem/is_valid_address/mr_manager_heap_search_pub, so
 *    the stage3_test_support.c stubs are NOT linked here (duplicate
 *    strong definitions).  The record groups cover: record replacement
 *    at one raw cell with a different width, pointer-over-primitive
 *    replacement with moved-array back-reference repair, exact-at-cap
 *    records and first-over-cap sticky flag handling, and parent
 *    sort/traversal using only the validated count.
 *
 *  - Owned-plan groups: exact legacy generic descriptors, resolver-backed
 *    NULL/fresh and non-NULL/NULL/OOB batches, typed-unavailable fallback,
 *    independent exact-size payloads, checked OOB arithmetic, allocation
 *    rollback, target-first child application, FIFO transitions, GLib queue-
 *    link allocator pairing, and total manager teardown.
 *
 * Build: see tests/osprey/Makefile (targets unit-stage7-mutation and
 * unit-stage7-mutation-asan).
 */

#include "qemu/osdep.h"
#include "osprey.h"
#include "osprey-internal.h"
#include "snapshot.h"
#include "provenance.h"
#include "qemu/thread.h"
#include "tcg/symbolic/symbolic-struct.h"
#include "stage7_mutation_reference.h"

#include <glib/gstdio.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/wait.h>

/* snapshot.c is compiled in for record/forkserver integration statics.  The
 * mutation owner itself is linked from snapshot-mutation.c as a separate
 * translation unit by the focused Makefile. */
#include "../../linux-user/snapshot.c"

/* The symbolic boundary advisor is compiled into this TU for the same reason:
 * its configuration and engine state are static, and the focused runner needs
 * to drive modes and budgets directly instead of exporting production setters.
 * The tracer build compiles the same source as its own translation unit
 * (linux-user/Makefile.objs), which is what proves the link boundary. */
#include "../../linux-user/snapshot-mutation-symbolic.c"

/* ------------------------------------------------------------------ */
/* Linker environment (externs snapshot.c and the OSPREY objects read) */
/* ------------------------------------------------------------------ */

unsigned long guest_base = 0;
uint64_t symbolic_start_code = 0;
uint64_t symbolic_end_code = 0;
Expr *pool = NULL;
Expr *next_free_expr = NULL;
Query *query_queue = NULL;
Query *next_query = NULL;
__thread CPUState *thread_cpu = NULL;
abi_ulong mmap_next_start = 0;
target_ulong target_brk = 0;
uint64_t last_translation_block = 0;

/* Host-environment stubs for snapshot.o's integration points.  The
 * record-level groups exercise the access-record paths only, not page
 * management or forkserver transport. */
void memcheck_init(void) {}
static abi_long test_mmap_result = -1;
static abi_ulong test_mmap_length;
static uint32_t test_mmap_calls;
abi_long target_mmap(abi_ulong start, abi_ulong len, int prot, int flags,
                     int fd, abi_ulong offset) {
    (void)start; (void)prot; (void)flags; (void)fd; (void)offset;
    test_mmap_calls++;
    test_mmap_length = len;
    return test_mmap_result;
}
int page_get_flags(target_ulong address) { (void)address; return 0; }
int walk_memory_regions(void *priv, walk_memory_regions_fn fn) {
    (void)priv; (void)fn;
    return 0;
}
void rcu_disable_atfork(void) {}

/* The focused runner never loads a cache manifest, but snapshot.c contains
 * that production path.  Keep its QAPI dependencies inert in this standalone
 * link rather than pulling the complete QEMU object graph into the unit. */
void qobject_destroy(QObject *obj) { (void)obj; }
bool qnum_get_try_uint(const QNum *qn, uint64_t *value) {
    (void)qn; (void)value;
    return false;
}
QObject *qobject_from_json_with_token_limit(const char *text,
                                            uint64_t token_limit,
                                            Error **errp) {
    (void)text; (void)token_limit; (void)errp;
    return NULL;
}
int64_t qdict_get_try_int(const QDict *dict, const char *key,
                          int64_t fallback) {
    (void)dict; (void)key;
    return fallback;
}
const char *qdict_get_try_str(const QDict *dict, const char *key) {
    (void)dict; (void)key;
    return NULL;
}
QObject *qdict_get(const QDict *dict, const char *key) {
    (void)dict; (void)key;
    return NULL;
}
size_t qlist_size(const QList *list) { (void)list; return 0; }
const char *error_get_pretty(const Error *err) { (void)err; return ""; }
void error_free(Error *err) { (void)err; }

/* No-op mutex stubs: the unit runner is single-threaded. */
void qemu_mutex_init(QemuMutex *m) { memset(m, 0, sizeof(*m)); }
void qemu_mutex_destroy(QemuMutex *m) { (void)m; }
void qemu_mutex_lock_impl(QemuMutex *m, const char *f, const int l) {
    (void)m; (void)f; (void)l;
}
void qemu_mutex_unlock_impl(QemuMutex *m, const char *f, const int l) {
    (void)m; (void)f; (void)l;
}
QemuMutexLockFunc qemu_mutex_lock_func = qemu_mutex_lock_impl;
QemuMutexTrylockFunc qemu_mutex_trylock_func = NULL;

/* ------------------------------------------------------------------ */
/* Test scaffolding                                                    */
/* ------------------------------------------------------------------ */

static unsigned failures;
static unsigned checks;

#define CHECK(_condition, _message) do {                                  \
    checks++;                                                              \
    if (!(_condition)) {                                                   \
        fprintf(stderr, "FAIL: %s (line %d)\n", (_message), __LINE__); \
        failures++;                                                        \
    }                                                                      \
} while (0)

/* Reinitialize the runtime catalogs so identity cases start from a
 * known state. */
static void reset_runtime(void)
{
    osprey_free_runtime_regions();
    provenance_init();
    osprey_set_image_bounds(0x400000, 0x401000);
    osprey_register_image_global(NULL, 0x402000, 0x1000); /* .data */
    osprey_register_image_global(NULL, 0x403000, 0x800);  /* .bss */
}

/* Register a live heap instance the same way the allocator hook does:
 * provenance object first, then osprey_on_alloc_success. */
static PtrTag make_heap(CPUArchState *env, target_ulong base,
                        target_ulong size, target_ulong site_pc)
{
    PtrTag t = provenance_create_object(base, size, site_pc,
                                        PROV_PRODUCER_MALLOC_RETURN);
    OspreyAllocatorObservation obs = {
        .kind = OSPREY_ALLOCATOR_MALLOC,
        .site_pc = site_pc,
        .requested_size = size,
    };
    osprey_on_alloc_success(env, &obs, base, t.object_id, t.generation);
    return t;
}

static void free_heap(CPUArchState *env, const PtrTag *t, target_ulong site_pc)
{
    osprey_on_free_identity(env, t->object_id, t->generation, site_pc);
    CHECK(provenance_retire_object(t->concrete_value),
          "provenance object retired by base");
}

/* ------------------------------------------------------------------ */
/* Capture matrix                                                      */
/* ------------------------------------------------------------------ */

/* Group 1: global, heap, and stack cell locators (both orders). */
static void test_cell_locators(void)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));

    /* Global: merged instance 0, image-relative offset. */
    OspreyRuntimeAddressRef gref;
    CHECK(osprey_capture_address_ref(env, 0x402008, &gref),
          "global capture");
    CHECK(gref.valid == 1 && gref.instance_id == 0 &&
          gref.prov_object_id == 0 && gref.prov_generation == 0,
          "global locator identity");
    CHECK(gref.address.region.kind == OSPREY_REGION_GLOBAL &&
          gref.address.offset == 0x2008 && gref.raw == 0x402008,
          "global canonical roundtrip");

    /* Heap: distinct instance + provenance pair. */
    PtrTag t = make_heap(env, 0x5000, 64, 0x400200);
    OspreyRuntimeAddressRef href;
    CHECK(osprey_capture_address_ref(env, 0x5010, &href),
          "heap capture");
    CHECK(href.valid == 1 && href.instance_id != 0,
          "heap instance id nonzero");
    CHECK(href.prov_object_id == t.object_id &&
          href.prov_generation == t.generation,
          "heap provenance pair");
    CHECK(href.address.region.kind == OSPREY_REGION_HEAP_SITE &&
          href.address.offset == 0x10 && href.raw == 0x5010,
          "heap canonical roundtrip");
    CHECK(href.address.region.site_offset == 0x200,
          "heap site normalized");

    /* Stack: two nested precise frames; the innermost wins with signed
     * offsets relative to its own entry SP. */
    osprey_on_call(env, 0x400300, 0x7ff000); /* outer frame */
    osprey_on_call(env, 0x400400, 0x7fef00); /* callee frame */
    osprey_on_rsp_update(env, 0x7feeec, 0x400410); /* callee grows */
    OspreyRuntimeAddressRef sref;
    CHECK(osprey_capture_address_ref(env, 0x7feeec, &sref),
          "stack capture");
    CHECK(sref.valid == 1 && sref.instance_id != 0,
          "stack instance id nonzero");
    CHECK(sref.address.region.kind == OSPREY_REGION_STACK_FUNCTION,
          "stack region kind");
    CHECK(sref.address.region.site_offset == 0x400,
          "callee site normalized");
    CHECK(sref.address.offset == (int64_t)0x7feeec - (int64_t)0x7fef00,
          "stack signed offset vs entry SP");

    /* Caller-frame address resolves to the outer frame, not the
     * callee: distinct instance id under the same canonical region
     * kind.  The caller address sits inside the caller's red-zone
     * window but above the callee entry SP, so the innermost-first
     * scan skips the callee. */
    OspreyRuntimeAddressRef cref;
    CHECK(osprey_capture_address_ref(env, 0x7fefb0, &cref),
          "caller-frame capture");
    CHECK(cref.valid == 1 && cref.instance_id != sref.instance_id,
          "caller and callee frames distinct instances");
    CHECK(cref.address.region.site_offset == 0x300,
          "caller site normalized");
    CHECK(cref.address.offset == (int64_t)0x7fefb0 - (int64_t)0x7ff000,
          "caller signed offset vs entry SP");

    /* Every captured locator round-trips raw<->canonical through the
     * instance anchor. */
    CHECK((target_ulong)((int64_t)(target_ulong)gref.raw -
                         gref.address.offset) == 0x402008 - 0x2008,
          "global anchor reconstructs raw");
    CHECK((target_ulong)((int64_t)href.raw - href.address.offset) == 0x5000,
          "heap anchor reconstructs raw");
    CHECK((target_ulong)((int64_t)sref.raw - sref.address.offset) ==
              0x7fef00,
          "stack anchor reconstructs raw");

    free_heap(env, &t, 0x400400);
    g_free(env);
}

/* Group 2: recursive same-site activations must never collapse. */
static void test_recursive_frames(void)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));

    osprey_on_call(env, 0x400300, 0x7ff000);
    OspreyRuntimeAddressRef r1;
    CHECK(osprey_capture_address_ref(env, 0x7feff8, &r1),
          "outer recursive frame capture");

    /* Recursion: same callee PC, lower entry SP. */
    osprey_on_call(env, 0x400300, 0x7fef00);
    osprey_on_rsp_update(env, 0x7feef0, 0x400310);
    OspreyRuntimeAddressRef r2;
    CHECK(osprey_capture_address_ref(env, 0x7feef8, &r2),
          "inner recursive frame capture");

    CHECK(r1.valid == 1 && r2.valid == 1, "both recursive frames");
    CHECK(r1.instance_id != r2.instance_id,
          "recursive activations distinct instance ids");
    CHECK(r1.address.region.kind == r2.address.region.kind &&
          r1.address.region.site_offset == r2.address.region.site_offset,
          "same canonical region (site)");
    CHECK(r1.address.offset == r2.address.offset,
          "same entry-relative offset");
    /* Region+offset alone cannot distinguish the two: the locator must
     * carry instance_id. */
    CHECK(r1.raw != r2.raw, "recursive raw addresses differ");

    g_free(env);
}

/* Group 3: two live same-site heap allocations. */
static void test_two_live_heaps(int order)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));

    PtrTag t1, t2;
    if (order == 0) {
        t1 = make_heap(env, 0x6000, 32, 0x400200);
        t2 = make_heap(env, 0x7000, 32, 0x400200);
    } else {
        t2 = make_heap(env, 0x7000, 32, 0x400200);
        t1 = make_heap(env, 0x6000, 32, 0x400200);
    }

    OspreyRuntimeAddressRef a1, a2;
    if (order == 0) {
        CHECK(osprey_capture_address_ref(env, 0x6008, &a1),
              "heap 1 capture (order 0)");
        CHECK(osprey_capture_address_ref(env, 0x7008, &a2),
              "heap 2 capture (order 0)");
    } else {
        CHECK(osprey_capture_address_ref(env, 0x7008, &a2),
              "heap 2 capture (order 1)");
        CHECK(osprey_capture_address_ref(env, 0x6008, &a1),
              "heap 1 capture (order 1)");
    }

    CHECK(a1.valid == 1 && a2.valid == 1, "both live heaps resolve");
    CHECK(a1.instance_id != a2.instance_id,
          "same-site live heaps distinct instance ids");
    CHECK(a1.address.region.kind == a2.address.region.kind &&
          a1.address.region.site_offset == a2.address.region.site_offset,
          "same site, so region identity collides");
    CHECK(a1.prov_object_id == t1.object_id &&
          a2.prov_object_id == t2.object_id,
          "provenance pair separates them");
    CHECK(a1.raw != a2.raw, "raw addresses differ");

    free_heap(env, &t1, 0x400400);
    free_heap(env, &t2, 0x400400);
    g_free(env);
}

/* Group 4: numeric heap-base reuse across provenance generations. */
static void test_base_reuse(void)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));

    PtrTag old = make_heap(env, 0x8000, 16, 0x400200);
    OspreyRuntimeAddressRef ref_old;
    CHECK(osprey_capture_address_ref(env, 0x8008, &ref_old),
          "old generation capture");
    uint64_t old_instance = ref_old.instance_id;
    CHECK(ref_old.prov_object_id == old.object_id, "old prov pair");

    free_heap(env, &old, 0x400400);
    PtrTag cur = make_heap(env, 0x8000, 64, 0x400200);
    OspreyRuntimeAddressRef ref_new;
    CHECK(osprey_capture_address_ref(env, 0x8008, &ref_new),
          "new generation capture");

    CHECK(ref_new.instance_id != old_instance,
          "reused base gets a fresh instance id");
    CHECK(ref_new.prov_object_id != old.object_id,
          "reused base gets a fresh provenance object");
    CHECK(ref_new.address.region.site_offset ==
              ref_old.address.region.site_offset,
          "same allocation site");

    free_heap(env, &cur, 0x400400);
    g_free(env);
}

/* A pair that remains LIVE in the object table is still stale when the
 * authoritative live-by-base index names a newer allocation. */
static void test_live_base_authority(void)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    PtrTag old = make_heap(env, 0x8800, 32, 0x400200);
    PtrTag newer = provenance_create_object(0x8800, 32, 0x400200,
                                             PROV_PRODUCER_MALLOC_RETURN);

    OspreyRuntimeAddressRef ref;
    CHECK(!osprey_capture_address_ref(env, 0x8808, &ref),
          "superseded live-by-base identity rejected");
    CHECK(ref.valid == 0, "superseded capture clears output");

    osprey_on_free_identity(env, old.object_id, old.generation, 0x400400);
    CHECK(provenance_retire_object(newer.concrete_value),
          "new authoritative provenance object retired");
    ProvenanceObject *old_object = provenance_lookup_object(
        old.object_id, old.generation);
    CHECK(old_object != NULL, "historical provenance object retained");
    if (old_object != NULL) {
        old_object->state = PROV_OBJ_FREED;
    }
    g_free(env);
}

/* Group 5 + 6: pointer target locator semantics. */
static void test_pointer_target_locator(int order)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));

    PtrTag t;
    /* Exercise both catalog insertion orders: the cell lives on the
     * stack and the target is the heap object. */
    if (order == 0) {
        t = make_heap(env, 0x9000, 64, 0x400200);
        osprey_on_call(env, 0x400300, 0x7ff000);
    } else {
        osprey_on_call(env, 0x400300, 0x7ff000);
        t = make_heap(env, 0x9000, 64, 0x400200);
    }

    OspreyRuntimeChunkRef cell;
    CHECK(osprey_capture_chunk_ref(env, 0x7feff8,
                                   (target_ulong)sizeof(target_ulong),
                                   &cell),
          order ? "pointer cell chunk (order 1)"
                : "pointer cell chunk (order 0)");
    CHECK(cell.start.valid == 1 && cell.size == sizeof(target_ulong),
          "cell locator width");

    /* Non-NULL target: address locator from the live target instance. */
    OspreyRuntimeAddressRef tref;
    CHECK(osprey_capture_address_ref(env, 0x9020, &tref),
          "target capture");
    CHECK(tref.prov_object_id == t.object_id && tref.instance_id != 0,
          "target locator from live instance");
    CHECK(tref.raw == 0x9020, "target raw address");

    /* NULL target: capture of 0 must fail (no fabricated locator). */
    OspreyRuntimeAddressRef nref;
    CHECK(!osprey_capture_address_ref(env, 0, &nref),
          "NULL target not capturable");
    CHECK(nref.valid == 0, "failed capture leaves zeroed locator");

    free_heap(env, &t, 0x400400);
    g_free(env);
}

/* Group 7: stale/freed heap target rejection. */
static void test_stale_target(void)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));

    PtrTag t = make_heap(env, 0xa000, 32, 0x400200);
    free_heap(env, &t, 0x400400);

    OspreyRuntimeAddressRef ref;
    CHECK(!osprey_capture_address_ref(env, 0xa008, &ref),
          "freed heap rejected");
    CHECK(ref.valid == 0, "freed capture leaves zeroed locator");

    g_free(env);
}

/* Disabled capture is still a failed capture and must clear caller-owned
 * output so a reused record cannot retain a stale valid locator. */
static void test_disabled_capture_clears_output(void)
{
    OspreyRuntimeAddressRef address;
    OspreyRuntimeChunkRef chunk;
    memset(&address, 0xa5, sizeof(address));
    memset(&chunk, 0xa5, sizeof(chunk));

    osprey_collect_enabled = 0;
    CHECK(!osprey_capture_address_ref(NULL, 0x402008, &address),
          "disabled address capture rejected");
    CHECK(!osprey_capture_chunk_ref(NULL, 0x402008, 8, &chunk),
          "disabled chunk capture rejected");
    osprey_collect_enabled = 1;

    OspreyRuntimeAddressRef zero_address;
    OspreyRuntimeChunkRef zero_chunk;
    memset(&zero_address, 0, sizeof(zero_address));
    memset(&zero_chunk, 0, sizeof(zero_chunk));
    CHECK(memcmp(&address, &zero_address, sizeof(address)) == 0,
          "disabled address capture clears output");
    CHECK(memcmp(&chunk, &zero_chunk, sizeof(chunk)) == 0,
          "disabled chunk capture clears output");
}

/* Group 8: interval rejection matrix. */
static void test_interval_rejection(void)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    PtrTag t = make_heap(env, 0xb000, 32, 0x400200);

    OspreyRuntimeChunkRef chunk;

    /* Zero width. */
    CHECK(!osprey_capture_chunk_ref(env, 0xb000, 0, &chunk),
          "zero width rejected");

    /* End overflow. */
    CHECK(!osprey_capture_chunk_ref(env, (target_ulong)-1, 2, &chunk),
          "end overflow rejected");

    /* Full-object interval valid; half-open end boundary. */
    CHECK(osprey_capture_chunk_ref(env, 0xb000, 32, &chunk),
          "full-object interval valid");
    CHECK(chunk.start.address.offset == 0 && chunk.size == 32,
          "full-object locator fields");
    CHECK(!osprey_capture_chunk_ref(env, 0xb018, 9, &chunk),
          "interval ending past object rejected");
    CHECK(!osprey_capture_chunk_ref(env, 0xb020, 1, &chunk),
          "one-past-end byte rejected");

    /* One-byte crossing into an unmapped neighbor: same as
     * one-past-end for a single byte. */
    CHECK(!osprey_capture_chunk_ref(env, 0xb020, 1, &chunk),
          "crossing out of instance rejected");

    free_heap(env, &t, 0x400400);
    g_free(env);
}

/* Cross-instance interval: both endpoints valid but different
 * instances -> rejected (identity reduction check). */
static void test_interval_cross_instance(int order)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));

    /* Two adjacent heaps; an interval spanning both must be rejected. */
    PtrTag t1, t2;
    if (order == 0) {
        t1 = make_heap(env, 0xc000, 8, 0x400200);
        t2 = make_heap(env, 0xc008, 8, 0x400200);
    } else {
        t2 = make_heap(env, 0xc008, 8, 0x400200);
        t1 = make_heap(env, 0xc000, 8, 0x400200);
    }

    OspreyRuntimeChunkRef chunk;
    CHECK(!osprey_capture_chunk_ref(env, 0xc000, 16, &chunk),
          order ? "cross-instance interval rejected (order 1)"
                : "cross-instance interval rejected (order 0)");

    /* Reduction-to-site check: the two heaps share the site; if the
     * chunk locator carried only region identity it would accept this
     * span.  Individual endpoints remain distinct instances. */
    OspreyRuntimeAddressRef r1, r2;
    bool resolved = order == 0
        ? osprey_capture_address_ref(env, 0xc000, &r1) &&
          osprey_capture_address_ref(env, 0xc008, &r2)
        : osprey_capture_address_ref(env, 0xc008, &r2) &&
          osprey_capture_address_ref(env, 0xc000, &r1);
    CHECK(resolved, "adjacent heaps individually resolvable");
    CHECK(r1.instance_id != r2.instance_id, "adjacent heaps distinct");

    free_heap(env, &t1, 0x400400);
    free_heap(env, &t2, 0x400400);
    g_free(env);
}

static void test_capture_matrix(void)
{
    test_disabled_capture_clears_output();
    test_live_base_authority();
    test_cell_locators();
    test_recursive_frames();
    test_base_reuse();
    test_stale_target();
    test_interval_rejection();
    for (int order = 0; order < 2; order++) {
        test_two_live_heaps(order);
        test_pointer_target_locator(order);
        test_interval_cross_instance(order);
    }
}

/* ------------------------------------------------------------------ */
/* Record-level groups (snapshot.c compiled in)                        */
/* ------------------------------------------------------------------ */

/* Simulated guest memory: the parent's analysis path dereferences
 * record addresses through g2h(), and the pointer path validates
 * targets against g_snapshot.pages.  One host allocation backs the
 * low guest addresses used by the record tests; record addresses must
 * stay inside [TEST_GUEST_BASE, TEST_GUEST_BASE + TEST_GUEST_SPAN). */
#define TEST_GUEST_SPAN (2u * 1024u * 1024u)
#define TEST_GUEST_BASE 0x10000000u
static void *test_guest_mem = NULL;

static void setup_guest_memory(void)
{
    test_guest_mem = g_malloc0(TEST_GUEST_SPAN);
    guest_base = (unsigned long)test_guest_mem - TEST_GUEST_BASE;
    /* Register the pages as snapshot-writable so is_valid_address(x,
     * true) accepts pointer targets. */
    for (target_ulong page = 0; page < TEST_GUEST_SPAN;
         page += SNAPSHOT_PAGE_SIZE) {
        SnapshotPageInfo *info = g_malloc0(sizeof(SnapshotPageInfo));
        info->addr = TEST_GUEST_BASE + page;
        info->perms = PAGE_READ | PAGE_WRITE;
        info->data = (void *)((unsigned long)test_guest_mem + page);
        g_hash_table_insert(g_snapshot.pages,
                            GSIZE_TO_POINTER(TEST_GUEST_BASE + page), info);
    }
}

static void teardown_guest_memory(void)
{
    guest_base = 0;
    if (test_guest_mem != NULL) {
        g_free(test_guest_mem);
        test_guest_mem = NULL;
    }
    if (g_snapshot.pages != NULL) {
        /* The pages table has a NULL value destroy: free the infos. */
        GHashTableIter it;
        gpointer key, value;
        g_hash_table_iter_init(&it, g_snapshot.pages);
        while (g_hash_table_iter_next(&it, &key, &value)) {
            g_free(value);
        }
        g_hash_table_remove_all(g_snapshot.pages);
    }
}

/* Drive snapshot_read_access the way the symbolic helpers do: a
 * SnapshotMemAccess with the loaded value copied into .target. */
static SnapshotReadToken record_access(CPUArchState *env, uintptr_t addr,
                                       target_ulong value, int size,
                                       bool symbolic)
{
    SnapshotMemAccess ma;
    memset(&ma, 0, sizeof(ma));
    ma.addr = addr;
    ma.size = (uintptr_t)size;
    ma.symbolic_value = symbolic;
    ma.observed_valid = true;
    ma.successful_load = true;
    ma.pc = 0x400100;
    memcpy(ma.target, &value, sizeof(target_ulong));
    return snapshot_read_access(env, &ma);
}

/* Reset the child-side record state (statics of snapshot.c are directly
 * reachable in this translation unit). */
static void reset_shared_records(void)
{
    snapshot_mutation_read_witness_disarm();
    if (shared_trace_data != NULL) {
        memset(shared_trace_data, 0, sizeof(SharedTraceData));
    }
    /* There is no ordered_map_destroy in snapshot.c; free the entries
     * (the table owns them) and the containers. */
    if (g_read_access_pointers != NULL) {
        g_hash_table_destroy(g_read_access_pointers->table);
        g_queue_free(g_read_access_pointers->queue);
        g_free(g_read_access_pointers);
        g_read_access_pointers = NULL;
    }
    if (g_read_access_tainted_primitives != NULL) {
        g_hash_table_destroy(g_read_access_tainted_primitives->table);
        g_queue_free(g_read_access_tainted_primitives->queue);
        g_free(g_read_access_tainted_primitives);
        g_read_access_tainted_primitives = NULL;
    }
    snapshot_modification_manager_reset(false);
}

/* Group 9: record replacement at one raw cell with a different width.
 * The heap catalog lives inside the simulated guest span so both the
 * capture path and the parent's g2h() dereference resolve. */
static void test_record_width_replacement(void)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    PtrTag t = make_heap(env, TEST_GUEST_BASE + 0x5000, 64, 0x400200);
    reset_shared_records();

    uintptr_t cell = TEST_GUEST_BASE + 0x5010;
    record_access(env, cell, 0, 8, true);
    CHECK(shared_trace_data->prim_idx == 1, "8-byte primitive recorded");
    CHECK(shared_trace_data->primitives[0].cell.start.valid == 1 &&
          shared_trace_data->primitives[0].cell.size == 8,
          "8-byte cell locator captured");
    CHECK(shared_trace_data->primitives[0].cell.start.address.offset == 0x10,
          "cell canonical offset");

    /* Same raw cell, 4-byte symbolic access: replacement updates both
     * width and locator consistently. */
    record_access(env, cell, 0, 4, true);
    CHECK(shared_trace_data->prim_idx == 1, "one record retained");
    CHECK(shared_trace_data->primitives[0].size == 4, "width replaced");
    CHECK(shared_trace_data->primitives[0].cell.size == 4,
          "locator width replaced consistently");

    /* Stale-locator check: retire the heap identity, then re-record at
     * the same cell.  The new record must carry NO stale locator. */
    free_heap(env, &t, 0x400400);
    record_access(env, cell, 0, 8, true);
    CHECK(shared_trace_data->primitives[0].cell.start.valid == 0,
          "stale identity leaves zeroed locator");

    reset_shared_records();
    g_free(env);
}

/* Group 10: pointer over primitive at one cell, then a later primitive
 * write at the same cell exercises the swap-removal path and the
 * moved-array back-reference repair.  The pointer writer itself does
 * NOT remove primitive records; the removal happens when a subsequent
 * primitive access finds a pointer entry at the aligned cell. */
static void test_pointer_over_primitive(void)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    PtrTag target_heap = make_heap(env, TEST_GUEST_BASE + 0x6000, 64,
                                   0x400200);
    /* A second heap hosts the pointer cell so the cell locator has a
     * live instance of its own (distinct from the target instance). */
    PtrTag cell_heap = make_heap(env, TEST_GUEST_BASE + 0x6800, 64,
                                 0x400300);
    reset_shared_records();

    uintptr_t cell = TEST_GUEST_BASE + 0x6820;
    target_ulong target = TEST_GUEST_BASE + 0x6020;

    /* 1. Primitive at a cell. */
    record_access(env, cell, 0, 8, true);
    CHECK(shared_trace_data->prim_idx == 1, "primitive first");

    /* 2. Pointer access at the same cell: records a pointer.  The
     * primitive record stays until the next primitive write finds the
     * pointer entry (removal happens on the primitive path). */
    record_access(env, cell, target, 8, false);
    CHECK(shared_trace_data->ptr_idx == 1, "pointer recorded");
    CHECK(shared_trace_data->pointers[0].cell.start.valid == 1 &&
              shared_trace_data->pointers[0].cell.start.prov_object_id ==
                  cell_heap.object_id,
          "pointer cell locator from cell instance");
    CHECK(shared_trace_data->pointers[0].target_ref.valid == 1 &&
          shared_trace_data->pointers[0].target_ref.prov_object_id ==
              target_heap.object_id,
          "target locator identity");
    CHECK(shared_trace_data->pointers[0].target_ref.raw == target,
          "target locator raw");
    CHECK(shared_trace_data->pointers[0].cell.start.instance_id !=
              shared_trace_data->pointers[0].target_ref.instance_id,
          "cell and target instances distinct");

    /* 3. Add five primitives at distinct cells (fills the array and
     * sets up the swap-removal move). */
    for (uintptr_t a = 0; a < 40; a += 8) {
        record_access(env, TEST_GUEST_BASE + 0x7100 + a, 0, 8, true);
    }
    CHECK(shared_trace_data->prim_idx == 6,
          "primitives recorded (stale one not yet removed)");

    /* 4. Primitive write at the pointer cell: the pointer entry
     * suppresses it and removes the stale primitive via swap-removal
     * (moves the last primitive into its slot, repairs the moved
     * back-reference). */
    record_access(env, cell, 0, 8, true);
    CHECK(shared_trace_data->prim_idx == 5,
          "primitive at pointer cell removed by swap-removal");

    /* All pointer records keep consistent locators after the moves. */
    for (uint32_t i = 0; i < shared_trace_data->ptr_idx; i++) {
        PointerAccess *p = &shared_trace_data->pointers[i];
        if (p->cell.start.valid) {
            CHECK(p->cell.size == 8, "pointer locator width");
            CHECK(p->target_ref.valid == 1 &&
                      p->target_ref.prov_object_id ==
                          target_heap.object_id,
                  "pointer target locator");
        }
    }
    /* No primitive record retained at the pointer cell. */
    for (uint32_t i = 0; i < shared_trace_data->prim_idx; i++) {
        PrimitiveAccess *p = &shared_trace_data->primitives[i];
        CHECK(p->addr != cell, "no stale primitive at pointer cell");
    }

    free_heap(env, &target_heap, 0x400400);
    free_heap(env, &cell_heap, 0x400400);
    reset_shared_records();
    g_free(env);
}

/* Group 11: exact-at-cap records, LRU recycling, and the defensive
 * over-cap path.  The defensive branch calls exit_with_status(1), so
 * it runs in a forked child; the sticky flag lives in MAP_SHARED
 * memory and survives into the parent. */
static void test_at_cap_sticky(void)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    reset_shared_records();

    /* Fill exactly to capacity. */
    for (int i = 0; i < MAX_PRIMITIVE_ACCESS; i++) {
        record_access(env, (uintptr_t)(TEST_GUEST_BASE + 0x8000 +
                                       8 * (uintptr_t)i), 0, 8, true);
    }
    CHECK(shared_trace_data->prim_idx == MAX_PRIMITIVE_ACCESS,
          "exactly at cap");
    CHECK(shared_trace_data->prim_overflow == 0, "no overflow at cap");

    /* One more distinct cell: LRU recycles the oldest shared_index, so
     * the counter stays at cap and nothing overflows. */
    record_access(env, (uintptr_t)(TEST_GUEST_BASE + 0x8000 - 8), 0, 8,
                  true);
    CHECK(shared_trace_data->prim_idx == MAX_PRIMITIVE_ACCESS,
          "index bounded after LRU recycling");
    CHECK(shared_trace_data->prim_overflow == 0,
          "LRU recycling does not set the sticky flag");

    /* Start a fresh record set for the defensive path: an ordered-map
     * entry whose shared_index points past the array (== MAX) trips
     * the writer's out-of-range branch, which sets the sticky flag and
     * exits.  Run it in a forked child while the queue is BELOW cap:
     * an LRU pop at cap would overwrite the injected shared_index
     * before the writer sees it. */
    reset_shared_records();
    CHECK(g_read_access_tainted_primitives == NULL,
          "record set cleared before defensive-path fork");
    pid_t pid = fork();
    CHECK(pid >= 0, "fork for defensive path");
    if (pid == 0) {
        if (g_read_access_tainted_primitives == NULL) {
            g_read_access_tainted_primitives =
                ordered_map_init(MAX_PRIMITIVE_ACCESS);
        }
        OrderedMapEntry *entry = g_new(OrderedMapEntry, 1);
        memset(entry, 0, sizeof(*entry));
        entry->key = TEST_GUEST_BASE + 0x9000;
        entry->shared_index = MAX_PRIMITIVE_ACCESS; /* out of range */
        g_hash_table_insert(g_read_access_tainted_primitives->table,
                            GSIZE_TO_POINTER(entry->key), entry);
        g_queue_push_tail(g_read_access_tainted_primitives->queue, entry);
        entry->node = g_read_access_tainted_primitives->queue->tail;
        record_access(env, entry->key, 0, 8, true);
        _exit(0); /* not reached: exit_with_status(1) fires first */
    }
    int wstatus = 0;
    CHECK(waitpid(pid, &wstatus, 0) == pid, "child reaped");
    CHECK(WIFEXITED(wstatus) && WEXITSTATUS(wstatus) == 1,
          "defensive path exits without a signal");
    CHECK(shared_trace_data->prim_overflow == 1,
          "defensive path sets sticky flag");

    /* A corrupted UINT32_MAX count must not become a negative signed
     * index and write before the fixed array. */
    reset_shared_records();
    pid = fork();
    CHECK(pid >= 0, "fork for extreme count");
    if (pid == 0) {
        shared_trace_data->prim_idx = UINT32_MAX;
        record_access(env, TEST_GUEST_BASE + 0x9010, 0, 8, true);
        _exit(0);
    }
    wstatus = 0;
    CHECK(waitpid(pid, &wstatus, 0) == pid, "extreme-count child reaped");
    CHECK(WIFEXITED(wstatus) && WEXITSTATUS(wstatus) == 1,
          "extreme count exits without out-of-bounds write");
    CHECK(shared_trace_data->prim_idx == UINT32_MAX,
          "writer does not advance corrupt count");
    CHECK(shared_trace_data->prim_overflow == 1,
          "extreme count sets sticky flag");

    reset_shared_records();
    pid = fork();
    CHECK(pid >= 0, "fork for extreme pointer count");
    if (pid == 0) {
        shared_trace_data->ptr_idx = UINT32_MAX;
        record_access(env, TEST_GUEST_BASE + 0x9018,
                      TEST_GUEST_BASE + 0x100, 8, false);
        _exit(0);
    }
    wstatus = 0;
    CHECK(waitpid(pid, &wstatus, 0) == pid,
          "extreme-pointer-count child reaped");
    CHECK(WIFEXITED(wstatus) && WEXITSTATUS(wstatus) == 1,
          "extreme pointer count exits without out-of-bounds write");
    CHECK(shared_trace_data->ptr_idx == UINT32_MAX,
          "pointer writer does not advance corrupt count");
    CHECK(shared_trace_data->ptr_overflow == 1,
          "extreme pointer count sets sticky flag");

    /* Removal from a corrupt empty record set must not underflow the
     * published count. */
    reset_shared_records();
    g_read_access_tainted_primitives =
        ordered_map_init(MAX_PRIMITIVE_ACCESS);
    OrderedMapEntry *entry = ordered_map_insert(
        g_read_access_tainted_primitives, TEST_GUEST_BASE + 0x9020, NULL);
    entry->shared_index = 0;
    remove_read_access_primitive(entry->key);
    CHECK(shared_trace_data->prim_idx == 0,
          "corrupt removal does not underflow count");
    CHECK(shared_trace_data->prim_overflow == 1,
          "corrupt removal sets sticky flag");

    reset_shared_records();
    g_free(env);
}

/* Group 10: read-event tokens.  Identity is epoch/lane/slot/access id, never
 * raw address, so replacement, lane change, or slot movement invalidates an
 * older token and finalization must abstain rather than attach symbolic
 * metadata to the wrong record. */
static void test_read_token_identity(void)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    reset_shared_records();

    uintptr_t a = TEST_GUEST_BASE + 0xa000;
    uintptr_t b = TEST_GUEST_BASE + 0xa100;
    uint64_t epoch = ++shared_trace_data->run_epoch;

    target_ulong value = 0x0000000011223344ULL;
    SnapshotReadToken t1 = record_access(env, a, value, 4, true);
    CHECK(t1.valid == 1 && t1.lane == SNAPSHOT_READ_LANE_PRIMITIVE &&
          t1.slot == 0 && t1.run_epoch == epoch,
          "primitive read returns a valid event token");
    CHECK(shared_trace_data->primitives[0].observed_read_valid == 1 &&
          memcmp(shared_trace_data->primitives[0].observed_read_bytes,
                 &value, 4) == 0,
          "record captures the exact child bytes at that width");
    CHECK(shared_trace_data->primitives[0].expr_index == -1 &&
          shared_trace_data->primitives[0].query_index == -1,
          "record starts without finalized symbolic indexes");

    CHECK(snapshot_finalize_read_token(t1, 40, 3, SNAPSHOT_ROOT_ZEXT),
          "finalizing the live token attaches its scalar metadata");
    CHECK(shared_trace_data->primitives[0].expr_index == 40 &&
          shared_trace_data->primitives[0].query_index == 3 &&
          shared_trace_data->primitives[0].root_extension ==
              SNAPSHOT_ROOT_ZEXT,
          "finalized indexes and extension are observable");

    /* Replacement at the same address changes the access id: the old token
     * no longer names the record and must not overwrite it. */
    SnapshotReadToken t2 = record_access(env, a, 0x55, 4, true);
    CHECK(t2.access_id != t1.access_id,
          "replacement issues a fresh access id");
    CHECK(shared_trace_data->primitives[0].expr_index == -1 &&
          shared_trace_data->primitives[0].query_index == -1 &&
          shared_trace_data->primitives[0].observed_read_valid == 1 &&
          shared_trace_data->primitives[0].observed_read_bytes[0] == 0x55,
          "replacement resets symbolic metadata and keeps new bytes");
    CHECK(!snapshot_finalize_read_token(t1, 41, 4, SNAPSHOT_ROOT_ZEXT),
          "stale token is rejected after replacement");
    CHECK(shared_trace_data->primitives[0].expr_index == -1,
          "stale finalization leaves the live record untouched");

    /* Width change is the same record identity only when the access id
     * matches; recording a different width reissues it. */
    SnapshotReadToken t3 = record_access(env, a, 0x77, 8, true);
    CHECK(!snapshot_finalize_read_token(t2, 42, 5, SNAPSHOT_ROOT_IDENTITY),
          "token is rejected after a width change");
    CHECK(snapshot_finalize_read_token(t3, 42, 5, SNAPSHOT_ROOT_IDENTITY),
          "current token finalizes after the width change");
    CHECK(shared_trace_data->primitives[0].size == 8 &&
          shared_trace_data->primitives[0].root_extension ==
              SNAPSHOT_ROOT_IDENTITY,
          "identity extension matches the machine-width load");

    /* Epoch change invalidates every token from the previous run. */
    shared_trace_data->run_epoch = epoch + 1;
    CHECK(!snapshot_finalize_read_token(t3, 43, 6, SNAPSHOT_ROOT_IDENTITY),
          "token is rejected across an epoch change");
    shared_trace_data->run_epoch = epoch;

    /* A non-retained read (not symbolic, non-pointer value) yields an
     * invalid token that can never finalize. */
    SnapshotReadToken none = record_access(env, b, 0x1234, 4, false);
    CHECK(none.valid == 0, "unretained read returns an invalid token");
    CHECK(!snapshot_finalize_read_token(none, 44, 7, SNAPSHOT_ROOT_ZEXT),
          "invalid token never finalizes");

    /* Out-of-range indexes are rejected before any record is touched. */
    SnapshotReadToken t4 = record_access(env, b, 0x9999, 4, true);
    CHECK(!snapshot_finalize_read_token(t4, -1, 7, SNAPSHOT_ROOT_ZEXT) &&
          !snapshot_finalize_read_token(t4, 44, -1, SNAPSHOT_ROOT_ZEXT) &&
          !snapshot_finalize_read_token(t4, 44, 7,
                                        (SnapshotRootExtension)7),
          "negative indexes and unknown extensions are rejected");
    CHECK(shared_trace_data->primitives[1].expr_index == -1,
          "rejected finalization leaves the record unchanged");

    /* Pointer-lane reads carry their own lane and finalize into their own
     * record; lane eligibility for symbolic advice is enforced later, by the
     * baseline copy, not here. */
    target_ulong ptr_target = TEST_GUEST_BASE + 0x10;
    SnapshotReadToken tp = record_access(env, b, ptr_target, 8, true);
    CHECK(tp.valid == 1 && tp.lane == SNAPSHOT_READ_LANE_POINTER,
          "pointer-valued read returns a pointer-lane token");
    CHECK(snapshot_finalize_read_token(tp, 50, 8, SNAPSHOT_ROOT_IDENTITY) &&
          shared_trace_data->pointers[tp.slot].expr_index == 50 &&
          shared_trace_data->pointers[tp.slot].query_index == 8 &&
          shared_trace_data->pointers[tp.slot].observed_read_valid == 1,
          "pointer-lane token finalizes into its own record");
    /* A primitive token must never be applied to the pointer lane: the lanes
     * are distinct record arrays and a mismatched lane abstains. */
    SnapshotReadToken crossed = t4;
    crossed.slot = tp.slot;
    CHECK(!snapshot_finalize_read_token(crossed, 51, 9,
                                        SNAPSHOT_ROOT_IDENTITY),
          "a primitive token cannot finalize against the pointer lane");

    g_free(env);
}

/* The B1 witness is a scalar exact-event diagnostic.  It reads only the
 * concrete bytes supplied by a successful load event and is independent of
 * whether the symbolic shadow survived to that load. */
static void test_mutation_read_witness_identity(void)
{
    CPUArchState *env = g_malloc0(sizeof(*env));
    SnapshotMutationBaseline baseline = {0};
    SnapshotMutationBaselineEntry entry = {0};
    SnapshotMutationPlan plan = {0};
    SnapshotMutationWrite write = {0};
    const uintptr_t cell = TEST_GUEST_BASE + 0xa200;
    const uintptr_t other = TEST_GUEST_BASE + 0xa208;
    const uint64_t baseline_epoch = 77;
    const uint32_t expected_value = 0x1000;

    reset_shared_records();
    baseline.run_epoch = baseline_epoch;
    baseline.entry_count = 1;
    baseline.entries = &entry;
    entry.token.run_epoch = baseline_epoch;
    entry.token.source_ordinal = 0;
    entry.lane = SNAPSHOT_MUTATION_LANE_PRIMITIVE;
    entry.source_kind = SNAPSHOT_MUTATION_SOURCE_PRIMITIVE;
    entry.access_id = 0;
    entry.pc = 0x400100;
    entry.addr = cell;
    entry.size = sizeof(expected_value);
    entry.observed_read_valid = true;
    entry.observed_read_bytes[0] = 1;
    write.kind = SNAPSHOT_MUTATION_BYTES;
    write.addr = cell;
    write.size = sizeof(expected_value);
    memcpy(write.value, &expected_value, sizeof(expected_value));
    plan.advisor_id = 1;
    plan.num_mods = 1;
    plan.mods = &write;
    snapshot_mutation_baseline = &baseline;
    shared_trace_data->run_epoch = 100;
    snapshot_mutation_plan_set_source(
        &plan, &baseline, entry.token,
        SNAPSHOT_MUTATION_SEED_OBSERVED_READ, true, 42);
    snapshot_mutation_read_witness_arm(&plan);

    /* A concrete retained load (symbolic_value=false) still proves exactly
     * the candidate bytes; witness matching cannot depend on taint. */
    SnapshotReadToken token = record_access(env, cell, expected_value, 4,
                                            false);
    CHECK(token.valid == 0 &&
          __atomic_load_n(&shared_trace_data->mutation_read_witness.state,
                          __ATOMIC_ACQUIRE) ==
              SNAPSHOT_MUTATION_READ_WITNESS_MATCHED_VALUE,
          "successful untainted load witnesses exact planned value");
    CHECK(shared_trace_data->prim_idx == 0,
          "witness does not retain a new symbolic read record");
    uint8_t duplicate_bytes[sizeof(expected_value)];
    memcpy(duplicate_bytes, &expected_value, sizeof(duplicate_bytes));
    snapshot_mutation_read_witness_observe(
        SNAPSHOT_MUTATION_LANE_PRIMITIVE, 0, entry.pc, (target_ulong)cell,
        sizeof(expected_value), 100, duplicate_bytes);
    CHECK(__atomic_load_n(&shared_trace_data->mutation_read_witness.state,
                          __ATOMIC_ACQUIRE) ==
              SNAPSHOT_MUTATION_READ_WITNESS_AMBIGUOUS,
          "duplicate exact event identity is ambiguous rather than positive");

    snapshot_mutation_baseline = NULL;
    reset_shared_records();
    snapshot_mutation_baseline = &baseline;
    shared_trace_data->run_epoch = 101;
    snapshot_mutation_read_witness_arm(&plan);
    (void)record_access(env, cell, 7, 4, false);
    CHECK(__atomic_load_n(&shared_trace_data->mutation_read_witness.state,
                          __ATOMIC_ACQUIRE) ==
              SNAPSHOT_MUTATION_READ_WITNESS_DIFFERENT_VALUE,
          "overwritten bytes report different-value rather than use");

    /* A same-PC event before the target read shifts its lane counter.  The
     * second same-PC access must not match by PC/address alone. */
    snapshot_mutation_baseline = NULL;
    reset_shared_records();
    snapshot_mutation_baseline = &baseline;
    shared_trace_data->run_epoch = 102;
    snapshot_mutation_read_witness_arm(&plan);
    (void)record_access(env, other, expected_value, 4, false);
    (void)record_access(env, cell, expected_value, 4, false);
    CHECK(shared_trace_data->prim_access_cnt == 2 &&
          __atomic_load_n(&shared_trace_data->mutation_read_witness.state,
                          __ATOMIC_ACQUIRE) ==
              SNAPSHOT_MUTATION_READ_WITNESS_UNKNOWN,
          "repeated PC with shifted event ID remains unknown");

    /* A descriptor from a stale frozen epoch cannot arm, and a live child
     * event from a different representative epoch cannot match an armed one. */
    snapshot_mutation_baseline = NULL;
    reset_shared_records();
    snapshot_mutation_baseline = &baseline;
    shared_trace_data->run_epoch = 103;
    SnapshotMutationReadWitnessDescriptor saved_witness = plan.read_witness;
    plan.read_witness.baseline_epoch = baseline_epoch - 1;
    snapshot_mutation_read_witness_arm(&plan);
    (void)record_access(env, cell, expected_value, 4, false);
    CHECK(!snapshot_child_read_witness_armed &&
          __atomic_load_n(&shared_trace_data->mutation_read_witness.state,
                          __ATOMIC_ACQUIRE) ==
              SNAPSHOT_MUTATION_READ_WITNESS_UNKNOWN,
          "stale baseline epoch cannot arm a witness");
    plan.read_witness = saved_witness;

    snapshot_mutation_baseline = NULL;
    reset_shared_records();
    snapshot_mutation_baseline = &baseline;
    shared_trace_data->run_epoch = 104;
    snapshot_mutation_read_witness_arm(&plan);
    shared_trace_data->run_epoch++;
    (void)record_access(env, cell, expected_value, 4, false);
    CHECK(__atomic_load_n(&shared_trace_data->mutation_read_witness.state,
                          __ATOMIC_ACQUIRE) ==
              SNAPSHOT_MUTATION_READ_WITNESS_UNKNOWN,
          "stale representative epoch cannot match an event");

    /* A new representative clears shared and child-local witness state and
     * restarts its lane event counters. */
    snapshot_mutation_baseline = NULL;
    reset_shared_records();
    snapshot_mutation_baseline = &baseline;
    shared_trace_data->run_epoch = 105;
    snapshot_mutation_read_witness_arm(&plan);
    (void)record_access(env, cell, expected_value, 4, false);
    snapshot_prepare_mutation_epoch();
    CHECK(!snapshot_child_read_witness_armed &&
          shared_trace_data->prim_access_cnt == 0 &&
          __atomic_load_n(&shared_trace_data->mutation_read_witness.state,
                          __ATOMIC_ACQUIRE) ==
              SNAPSHOT_MUTATION_READ_WITNESS_UNKNOWN,
          "representative reset clears witness and access counters");
    (void)record_access(env, cell, expected_value, 4, false);
    CHECK(__atomic_load_n(&shared_trace_data->mutation_read_witness.state,
                          __ATOMIC_ACQUIRE) ==
              SNAPSHOT_MUTATION_READ_WITNESS_UNKNOWN,
          "previous representative witness is not reused");

    snapshot_mutation_read_witness_disarm();
    snapshot_mutation_baseline = NULL;
    g_free(env);
}

/* A valid bounded record whose locator is unavailable must retain the
 * existing generic mutation descriptors and order. */
static void test_generic_without_locator(void)
{
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    reset_shared_records();

    uintptr_t cell = TEST_GUEST_BASE + 0x9800;
    osprey_collect_enabled = 0;
    record_access(env, cell, 0, 8, true);
    osprey_collect_enabled = 1;
    CHECK(shared_trace_data->prim_idx == 1,
          "generic-only record retained");
    CHECK(shared_trace_data->primitives[0].cell.start.valid == 0,
          "generic-only record has no locator");
    shared_trace_data->exit_info.valid = 1;

    ArgumentInfo arg_info[1] = {{0, "rax", 0, NULL}};
    int remaining = analyze_collected_data(arg_info, 0);
    CHECK(mod_manager != NULL && mod_manager->current != NULL,
          "generic-only record selects a candidate");
    if (mod_manager != NULL && mod_manager->current != NULL) {
        SnapshotMutationWrite *candidate = &mod_manager->current->mods[0];
        CHECK(candidate->addr == cell && candidate->size == 8 &&
              candidate->kind == SNAPSHOT_MUTATION_BYTES,
              "generic-only descriptor unchanged");
        CHECK(g_queue_get_length(mod_manager->modifications) == 1 &&
              remaining == 2,
              "generic-only candidate order/count unchanged");
    }

    reset_shared_records();
    g_free(env);
}

/* Group 12: parent sort/traversal uses only a validated count.  An
 * over-cap count does not identify an initialized prefix, so the parent
 * must reject that array entirely rather than sort or synthesize generic
 * candidates from zeroed/unpublished slots. */
static void test_parent_count_clamp(void)
{
    pid_t pid = fork();
    if (pid == 0) {
        _exit(snapshot_mutation_baseline_build(NULL, NULL, 0) == NULL ? 0 : 2);
    }
    int status = 0;
    CHECK(pid > 0 && waitpid(pid, &status, 0) == pid &&
              WIFEXITED(status) && WEXITSTATUS(status) == 0,
          "missing observation view is rejected without a crash");
    reset_runtime();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    reset_shared_records();

    uintptr_t base = TEST_GUEST_BASE + 0xa000;
    record_access(env, base, 0, 8, true);
    record_access(env, base + 8, 0, 8, true);
    record_access(env, base + 0x10, 0, 8, true);
    CHECK(shared_trace_data->prim_idx == 3, "three records");

    /* Simulate a corrupted counter plus the sticky overflow flag.  The
     * three real records are no longer distinguishable from an invented
     * prefix, so the parent must consume none of this array. */
    shared_trace_data->prim_idx = MAX_PRIMITIVE_ACCESS + 7;
    shared_trace_data->prim_overflow = 1;
    shared_trace_data->exit_info.valid = 1;

    ArgumentInfo arg_info[1] = {{0, "rax", 0, NULL}};
    int remaining = analyze_collected_data(arg_info, 0);

    CHECK(mod_manager == NULL && mutation_analysis_started,
          "empty corrupt input destroys the exhausted manager");
    CHECK(remaining == 0, "corrupt count reports no remaining work");
    CHECK(g_read_access_tainted_primitives_all == NULL ||
              g_hash_table_size(g_read_access_tainted_primitives_all) == 0,
          "corrupt count traverses no primitive records");

    reset_shared_records();
    g_free(env);
}

/* ------------------------------------------------------------------ */
/* Stage 7.3 owned-plan groups                                         */
/* ------------------------------------------------------------------ */

static void free_plan_queue(GQueue *queue)
{
    if (queue != NULL) {
        g_queue_free_full(queue, (GDestroyNotify)snapshot_mutation_free);
    }
}

typedef struct MutationTypedFixture {
    OspreyContext *ctx;
    OspreyContext *previous_ctx;
    OspreyMutationModel model;
    OspreyMutationEntry entry;
    OspreyRuntimeChunkRef cell;
    OspreyRuntimeAddressRef target;
    OspreyRegionId global_region;
    OspreyRegionId target_region;
} MutationTypedFixture;

static OspreyRegionId mutation_region(OspreyRegionKind kind, uint64_t site)
{
    OspreyRegionId region;
    memset(&region, 0, sizeof(region));
    region.kind = kind;
    region.site_offset = site;
    return region;
}

static OspreyAddress mutation_address(OspreyRegionId region, int64_t offset)
{
    OspreyAddress address;
    memset(&address, 0, sizeof(address));
    address.region = region;
    address.offset = offset;
    return address;
}

static OspreyChunk mutation_chunk(OspreyRegionId region, int64_t offset,
                                  uint64_t size)
{
    OspreyChunk chunk;
    memset(&chunk, 0, sizeof(chunk));
    chunk.address = mutation_address(region, offset);
    chunk.size = size;
    return chunk;
}

static void mutation_append_instance(OspreyContext *ctx,
                                     OspreyRegionId region,
                                     uint64_t instance_id,
                                     uint64_t raw_base, uint64_t raw_min,
                                     uint64_t raw_max, uint64_t object_id,
                                     uint32_t generation)
{
    OspreyRegionInstance instance;
    memset(&instance, 0, sizeof(instance));
    instance.region = region;
    instance.instance_id = instance_id;
    instance.raw_base = raw_base;
    instance.raw_min = raw_min;
    instance.raw_max = raw_max;
    instance.prov_object_id = object_id;
    instance.prov_generation = generation;
    instance.sample_support = 1;
    g_array_append_val(ctx->region_instances, instance);
}

static void mutation_typed_fixture_init(MutationTypedFixture *fixture,
                                        uint64_t extent)
{
    OspreyConfig config;
    memset(&config, 0, sizeof(config));
    config.enabled = true;
    config.analysis_mode = OSPREY_ANALYSIS_MODE_MUTATION;
    config.shared_bytes = 1u << 20;
    config.max_facts = 1024;
    config.max_chunks_per_region = 128;
    config.max_candidates_per_kind_region = 4096;
    config.max_variables = 1024;
    config.max_factors = 4096;
    config.max_exact_clique_vars = 20;
    config.max_exact_table_bytes = 1u << 20;
    config.max_bp_table_bytes = 1u << 20;
    config.report_threshold = 0.6;

    memset(fixture, 0, sizeof(*fixture));
    fixture->previous_ctx = g_osprey_ctx;
    fixture->ctx = osprey_new(&config);
    fixture->global_region = mutation_region(OSPREY_REGION_GLOBAL, 0);
    fixture->target_region = mutation_region(OSPREY_REGION_HEAP_SITE, 0x400);

    mutation_append_instance(fixture->ctx, fixture->global_region, 0,
                             TEST_GUEST_BASE, TEST_GUEST_BASE,
                             TEST_GUEST_BASE + TEST_GUEST_SPAN, 0, 0);
    mutation_append_instance(fixture->ctx, fixture->target_region, 7,
                             TEST_GUEST_BASE + 0x5000,
                             TEST_GUEST_BASE + 0x5000,
                             TEST_GUEST_BASE + 0x6000, 0xabc, 3);

    fixture->entry.cell = mutation_chunk(fixture->global_region, 0xb000,
                                          sizeof(target_ulong));
    fixture->entry.target_base = mutation_address(fixture->target_region, 0);
    fixture->entry.extent = extent;
    fixture->entry.support = 1;
    fixture->entry.ordinal = 0;
    fixture->entry.kind = OSPREY_MUTATION_AGGREGATE_STRUCT;

    fixture->model.version = OSPREY_MUTATION_MODEL_VERSION;
    fixture->model.entry_count = 1;
    fixture->model.publication_valid = 1;
    fixture->model.entries = &fixture->entry;

    fixture->cell.start.address = fixture->entry.cell.address;
    fixture->cell.start.raw = TEST_GUEST_BASE + 0xb000;
    fixture->cell.start.instance_id = 0;
    fixture->cell.start.valid = 1;
    fixture->cell.size = sizeof(target_ulong);

    fixture->target.address = fixture->entry.target_base;
    fixture->target.raw = TEST_GUEST_BASE + 0x5000;
    fixture->target.instance_id = 7;
    fixture->target.prov_object_id = 0xabc;
    fixture->target.prov_generation = 3;
    fixture->target.valid = 1;

    fixture->ctx->mutation_model = &fixture->model;
    fixture->ctx->mutation_model_ready = true;
    fixture->ctx->mutation_runtime_ready = false;
    fixture->ctx->tx_status = OSPREY_OK;
    fixture->ctx->tx_model_ready = true;
    g_osprey_ctx = fixture->ctx;
    CHECK(osprey_runtime_index_build(fixture->ctx),
          "typed mutation runtime index builds");
    CHECK(osprey_runtime_mutation_prepare(fixture->ctx),
          "typed mutation compact publication validates");
}

static void mutation_typed_fixture_free(MutationTypedFixture *fixture)
{
    if (fixture->ctx == NULL) return;
    fixture->ctx->mutation_model = NULL;
    fixture->ctx->mutation_model_ready = false;
    fixture->ctx->mutation_runtime_ready = false;
    fixture->ctx->tx_model_ready = false;
    osprey_free(fixture->ctx);
    fixture->ctx = NULL;
    g_osprey_ctx = fixture->previous_ctx;
    osprey_ctx_ref_set(fixture->previous_ctx);
    fixture->previous_ctx = NULL;
}

static void test_owned_generic_plan_parity(void)
{
    static const uint32_t widths[] = {1, 2, 3, 4, 8};
    for (size_t wi = 0; wi < G_N_ELEMENTS(widths); wi++) {
        MutationCandidate source;
        memset(&source, 0x5a, sizeof(source));
        source.addr = wi == 0 ? 3 : TEST_GUEST_BASE + 0xa800 + wi * 8;
        source.size = widths[wi];
        source.kind = 0;
        source.expr = (Expr *)(uintptr_t)0x1234;
        MutationCandidate before = source;
        GQueue *queue = g_queue_new();

        snapshot_mutation_test_set_alloc_fail_after(-1);
        bool queued = add_modification_primitive(queue, &source);
        CHECK(queued, "generic plan batch queued");
        CHECK(memcmp(&source, &before, sizeof(source)) == 0,
              "generic planning leaves source unchanged");
        CHECK(g_queue_get_length(queue) == (widths[wi] == 3 ? 1 : 3),
              "generic plan count matches legacy order");

        uint32_t ordinal = 0;
        for (GList *node = queue->head; node != NULL; node = node->next) {
            SnapshotMutationPlan *modification = node->data;
            CHECK(modification->num_mods == 1,
                  "generic queue entries have one owned write");
            SnapshotMutationWrite *write = &modification->mods[0];
            CHECK(write->kind == SNAPSHOT_MUTATION_BYTES &&
                  write->addr == source.addr && write->size == source.size &&
                  write->expr_index == -1 && write->query_index == -1 &&
                  write->target.bytes == NULL &&
                  write->target.extent == 0,
                  "generic plan descriptor is private and inactive-target clean");
            if (source.size == 3) {
                uint8_t expected[sizeof(source.value)];
                memcpy(expected, source.value, sizeof(expected));
                flip_bits(expected, source.size);
                CHECK(memcmp(write->value, expected, sizeof(expected)) == 0,
                      "default-width plan preserves bit-flip bytes");
            } else if (ordinal == 0) {
                uint8_t expected[sizeof(source.value)];
                memcpy(expected, source.value, sizeof(expected));
                memset(expected, 0, source.size);
                CHECK(memcmp(write->value, expected, sizeof(expected)) == 0,
                      "zero plan bytes match source width");
            } else if (ordinal == 1) {
                uint8_t expected[sizeof(source.value)];
                memcpy(expected, source.value, sizeof(expected));
                memset(expected, 0, source.size);
                expected[0] = 1;
                CHECK(memcmp(write->value, expected, sizeof(expected)) == 0,
                      "one plan bytes match source width");
            } else {
                uint8_t expected[sizeof(source.value)];
                memcpy(expected, source.value, sizeof(expected));
                /* Preserve the legacy descriptors, not the intended
                 * algorithm: the old one-byte path flipped a zeroed
                 * working value, and the old two-byte path flipped the
                 * value after replacing it with one. */
                if (source.size == 1) {
                    expected[0] = 0;
                } else if (source.size == 2) {
                    expected[0] = 1;
                    expected[1] = 0;
                }
                flip_bits(expected, source.size);
                CHECK(memcmp(write->value, expected, sizeof(expected)) == 0,
                      "bit-flip plan preserves legacy descriptor");
            }
            ordinal++;
        }
        free_plan_queue(queue);
    }
}

static void test_owned_generic_boundary_parity(void)
{
    static const struct {
        uint32_t size;
        uint64_t original;
        uint32_t count;
        uint64_t expected[3];
    } cases[] = {
        {1, 0, 2, {1, UINT8_MAX}},
        {1, 1, 2, {0, UINT8_MAX}},
        {2, 0, 2, {1, UINT16_MAX - 1}},
        {2, 1, 2, {0, UINT16_MAX - 1}},
        {3, 0x030201, 1, {0xfcfdfe}},
        {4, 0, 2, {1, UINT32_MAX}},
        {4, 1, 2, {0, UINT32_MAX - 1}},
        {8, 0, 2, {1, UINT64_MAX}},
        {8, 1, 2, {0, UINT64_MAX - 1}},
    };

    for (size_t ci = 0; ci < G_N_ELEMENTS(cases); ci++) {
        MutationCandidate source = {0};
        source.addr = TEST_GUEST_BASE + 0xaa00 + ci * 8;
        source.size = cases[ci].size;
        source.expr = (Expr *)(uintptr_t)(0x2000 + ci);
        memcpy(source.value, &cases[ci].original, source.size);
        MutationCandidate before = source;
        GQueue *queue = g_queue_new();

        CHECK(add_modification_primitive(queue, &source),
              "boundary generic batch queued");
        CHECK(memcmp(&source, &before, sizeof(source)) == 0,
              "boundary generic source remains immutable");
        CHECK(g_queue_get_length(queue) == cases[ci].count,
              "boundary generic plan count matches legacy");

        uint32_t ordinal = 0;
        for (GList *node = queue->head; node != NULL; node = node->next) {
            SnapshotMutationPlan *modification = node->data;
            uint8_t expected[sizeof(target_ulong)] = {0};
            memcpy(expected, &cases[ci].expected[ordinal], source.size);
            CHECK(modification->num_mods == 1 &&
                  modification->mods[0].kind == SNAPSHOT_MUTATION_BYTES &&
                  modification->mods[0].size == source.size &&
                  memcmp(modification->mods[0].value, expected,
                         source.size) == 0,
                  "boundary generic descriptor matches legacy oracle");
            ordinal++;
        }
        free_plan_queue(queue);
    }
}

static void test_owned_untyped_pointer_parity(void)
{
    MutationCandidate source = {0};
    source.addr = TEST_GUEST_BASE + 0xaac0;
    source.size = sizeof(target_ulong);
    source.kind = 1;
    source.expr = (Expr *)(uintptr_t)0x4567;
    target_ulong original = TEST_GUEST_BASE + 0x100;
    memcpy(source.value, &original, sizeof(original));
    MutationCandidate before = source;
    GQueue *queue = g_queue_new();

    CHECK(add_untyped_pointer_candidate(queue, &source),
          "untyped pointer plan queued");
    CHECK(memcmp(&source, &before, sizeof(source)) == 0,
          "untyped pointer source remains immutable");
    CHECK(g_queue_get_length(queue) == 1,
          "untyped pointer keeps one legacy null plan");
    if (!g_queue_is_empty(queue)) {
        SnapshotMutationPlan *modification = g_queue_peek_head(queue);
        target_ulong value = UINT64_MAX;
        memcpy(&value, modification->mods[0].value, sizeof(value));
        CHECK(modification->num_mods == 1 &&
              modification->mods[0].kind == SNAPSHOT_MUTATION_POINTER_NULL &&
              modification->mods[0].addr == source.addr &&
              modification->mods[0].size == sizeof(target_ulong) &&
              modification->mods[0].expr_index == -1 &&
              modification->mods[0].query_index == -1 && value == 0 &&
              modification->mods[0].target.bytes == NULL &&
              modification->mods[0].target.extent == 0,
              "untyped pointer descriptor preserves null fallback");
    }
    free_plan_queue(queue);

    queue = g_queue_new();
    snapshot_mutation_test_set_alloc_fail_after(0);
    CHECK(!add_untyped_pointer_candidate(queue, &source),
          "untyped pointer allocation failure is reported");
    snapshot_mutation_test_set_alloc_fail_after(-1);
    CHECK(g_queue_is_empty(queue) &&
          memcmp(&source, &before, sizeof(source)) == 0,
          "untyped pointer failure leaves queue and source unchanged");
    free_plan_queue(queue);
}

static void test_owned_fresh_payloads(void)
{
    MutationCandidate source;
    memset(&source, 0, sizeof(source));
    source.addr = TEST_GUEST_BASE + 0xab00;
    source.size = sizeof(target_ulong);
    source.kind = 1;
    source.expr = (Expr *)(uintptr_t)0x5678;
    uint8_t zero[sizeof(target_ulong)] = {0};
    uint8_t ones[sizeof(target_ulong)];
    memset(ones, 1, sizeof(ones));
    SnapshotMutationPlan *batch[2] = {
        snapshot_mutation_new(&source, SNAPSHOT_MUTATION_POINTER_FRESH,
                              zero, source.size, sizeof(zero), zero),
        snapshot_mutation_new(&source, SNAPSHOT_MUTATION_POINTER_FRESH,
                              zero, source.size, sizeof(ones), ones),
    };
    GQueue *queue = g_queue_new();
    CHECK(batch[0] != NULL && batch[1] != NULL,
          "fresh plans allocate independently");
    CHECK(snapshot_mutation_enqueue_batch(queue, batch, 2),
          "fresh plan batch enqueues atomically");
    if (g_queue_get_length(queue) == 2) {
        SnapshotMutationPlan *first = g_queue_peek_nth(queue, 0);
        SnapshotMutationPlan *second = g_queue_peek_nth(queue, 1);
        CHECK(first->mods[0].target.bytes != second->mods[0].target.bytes,
              "fresh target payloads do not alias");
        CHECK(memcmp(first->mods[0].target.bytes, zero, sizeof(zero)) == 0 &&
              memcmp(second->mods[0].target.bytes, ones, sizeof(ones)) == 0,
              "fresh target payloads retain independent fills");
        CHECK(first->mods[0].value[0] == 0 &&
              second->mods[0].value[0] == 0,
              "fresh cell bytes remain immutable placeholders");
    }
    free_plan_queue(queue);
}

static bool bytes_equal_value(const uint8_t *bytes, uint64_t size,
                              uint8_t value)
{
    for (uint64_t i = 0; i < size; i++) {
        if (bytes[i] != value) return false;
    }
    return true;
}

static void test_typed_pointer_plans_and_fallback(void)
{
    MutationTypedFixture fixture;
    mutation_typed_fixture_init(&fixture, 13);

    MutationCandidate source;
    memset(&source, 0, sizeof(source));
    source.addr = fixture.cell.start.raw;
    source.size = sizeof(target_ulong);
    source.expr = (Expr *)(uintptr_t)0x7654;
    MutationCandidate before = source;

    static const uint8_t fills[] = {0x00, 0x01, 0xff};
    for (uint32_t source_kind = SNAPSHOT_POINTER_FROM_PRIMITIVE;
         source_kind <= SNAPSHOT_POINTER_FROM_ACCESS; source_kind++) {
        GQueue *queue = g_queue_new();
        CHECK(add_pointer_typed_candidate(
                  queue, &source, &fixture.cell, NULL, true,
                  (SnapshotPointerSource)source_kind),
              "NULL typed pointer batch queues");
        CHECK(g_queue_get_length(queue) == 3,
              "NULL typed pointer has exactly three variants");
        for (uint32_t i = 0; i < G_N_ELEMENTS(fills); i++) {
            SnapshotMutationPlan *modification = g_queue_peek_nth(queue, i);
            SnapshotMutationWrite *write = &modification->mods[0];
            CHECK(write->kind == SNAPSHOT_MUTATION_POINTER_FRESH &&
                  write->size == sizeof(target_ulong) &&
                  write->target.extent == 13 &&
                  write->target.bytes != NULL &&
                  bytes_equal_value(write->target.bytes, 13, fills[i]),
                  "NULL typed pointer owns the exact fill variant");
            CHECK(memcmp(write->value, source.value,
                         sizeof(write->value)) == 0,
                  "fresh pointer cell retains an immutable placeholder");
            if (i != 0) {
                SnapshotMutationPlan *previous = g_queue_peek_nth(queue, i - 1);
                CHECK(write->target.bytes != previous->mods[0].target.bytes,
                      "fresh pointer payloads are independently owned");
            }
        }
        CHECK(memcmp(&source, &before, sizeof(source)) == 0,
              "NULL typed planning leaves its source immutable");
        free_plan_queue(queue);
    }

    static const uint64_t other_extents[] = {
        1, sizeof(target_ulong), SNAPSHOT_PAGE_SIZE,
    };
    for (uint32_t i = 0; i < G_N_ELEMENTS(other_extents); i++) {
        fixture.entry.extent = other_extents[i];
        GQueue *queue = g_queue_new();
        CHECK(add_pointer_typed_candidate(
                  queue, &source, &fixture.cell, NULL, true,
                  SNAPSHOT_POINTER_FROM_ACCESS),
              "fresh extent boundary batch queues");
        CHECK(g_queue_get_length(queue) == 3,
              "fresh extent boundary retains three variants");
        for (uint32_t variant = 0; variant < G_N_ELEMENTS(fills); variant++) {
            SnapshotMutationPlan *modification = g_queue_peek_nth(queue, variant);
            CHECK(modification->mods[0].target.extent == other_extents[i] &&
                  bytes_equal_value(modification->mods[0].target.bytes,
                                    other_extents[i], fills[variant]),
                  "fresh extent boundary owns complete fill bytes");
        }
        free_plan_queue(queue);
    }
    fixture.entry.extent = 13;

    target_ulong concrete = fixture.target.raw;
    memcpy(source.value, &concrete, sizeof(concrete));
    before = source;
    GQueue *queue = g_queue_new();
    CHECK(add_pointer_typed_candidate(
              queue, &source, &fixture.cell, &fixture.target, true,
              SNAPSHOT_POINTER_FROM_ACCESS),
          "non-NULL typed pointer batch queues");
    CHECK(g_queue_get_length(queue) == 2,
          "non-NULL typed pointer has exactly NULL and OOB variants");
    if (g_queue_get_length(queue) == 2) {
        SnapshotMutationPlan *null_mod = g_queue_peek_nth(queue, 0);
        SnapshotMutationPlan *oob_mod = g_queue_peek_nth(queue, 1);
        target_ulong null_value = UINT64_MAX;
        target_ulong oob_value = 0;
        memcpy(&null_value, null_mod->mods[0].value, sizeof(null_value));
        memcpy(&oob_value, oob_mod->mods[0].value, sizeof(oob_value));
        CHECK(null_mod->mods[0].kind == SNAPSHOT_MUTATION_POINTER_NULL &&
              null_value == 0 && null_mod->mods[0].target.bytes == NULL,
              "non-NULL typed NULL descriptor is exact");
        CHECK(oob_mod->mods[0].kind == SNAPSHOT_MUTATION_POINTER_OOB &&
              oob_value == concrete + 13 + 0x10 &&
              oob_mod->mods[0].target.bytes == NULL,
              "non-NULL typed OOB descriptor uses checked target end");
    }
    CHECK(memcmp(&source, &before, sizeof(source)) == 0,
          "non-NULL typed planning leaves its source immutable");
    free_plan_queue(queue);

    memset(source.value, 0, sizeof(source.value));
    queue = g_queue_new();
    CHECK(add_pointer_typed_candidate(
              queue, &source, &fixture.cell, NULL, false,
              SNAPSHOT_POINTER_FROM_PRIMITIVE),
          "untrusted primitive record falls back generically");
    CHECK(g_queue_get_length(queue) == 2 &&
          ((SnapshotMutationPlan *)g_queue_peek_head(queue))->mods[0].kind ==
              SNAPSHOT_MUTATION_BYTES,
          "sticky record failure disables typed primitive planning");
    free_plan_queue(queue);

    queue = g_queue_new();
    CHECK(add_pointer_typed_candidate(
              queue, &source, &fixture.cell, NULL, false,
              SNAPSHOT_POINTER_FROM_ACCESS),
          "untrusted pointer record falls back generically");
    CHECK(g_queue_get_length(queue) == 1 &&
          ((SnapshotMutationPlan *)g_queue_peek_head(queue))->mods[0].kind ==
              SNAPSHOT_MUTATION_POINTER_NULL,
          "sticky record failure preserves untyped pointer behavior");
    free_plan_queue(queue);

    MutationCandidate mismatched = source;
    mismatched.addr++;
    queue = g_queue_new();
    CHECK(add_pointer_typed_candidate(
              queue, &mismatched, &fixture.cell, NULL, true,
              SNAPSHOT_POINTER_FROM_ACCESS),
          "mismatched cell locator falls back generically");
    CHECK(g_queue_get_length(queue) == 1 &&
          ((SnapshotMutationPlan *)g_queue_peek_head(queue))->mods[0].kind ==
              SNAPSHOT_MUTATION_POINTER_NULL,
          "typed planning binds the locator to the mutation address");
    free_plan_queue(queue);

    fixture.entry.extent = 0;
    queue = g_queue_new();
    CHECK(add_pointer_typed_candidate(
              queue, &source, &fixture.cell, NULL, true,
              SNAPSHOT_POINTER_FROM_ACCESS),
          "zero-size target falls back generically");
    CHECK(g_queue_get_length(queue) == 1 &&
          ((SnapshotMutationPlan *)g_queue_peek_head(queue))->mods[0].kind ==
              SNAPSHOT_MUTATION_POINTER_NULL,
          "zero-size target preserves one untyped pointer plan");
    free_plan_queue(queue);

    fixture.entry.extent = SNAPSHOT_PAGE_SIZE + 1;
    queue = g_queue_new();
    CHECK(add_pointer_typed_candidate(
              queue, &source, &fixture.cell, NULL, true,
              SNAPSHOT_POINTER_FROM_ACCESS),
          "oversized target falls back generically");
    CHECK(g_queue_get_length(queue) == 1 &&
          ((SnapshotMutationPlan *)g_queue_peek_head(queue))->mods[0].kind ==
              SNAPSHOT_MUTATION_POINTER_NULL,
          "fresh target cap preserves one untyped pointer plan");
    free_plan_queue(queue);

    mutation_append_instance(fixture.ctx, fixture.target_region, 8,
                             UINT64_MAX - 31, UINT64_MAX - 31, UINT64_MAX,
                             0xdef, 4);
    CHECK(osprey_runtime_index_build(fixture.ctx),
          "near-limit target instance enters the runtime index");
    fixture.target.raw = UINT64_MAX - 31;
    fixture.target.instance_id = 8;
    fixture.target.prov_object_id = 0xdef;
    fixture.target.prov_generation = 4;
    fixture.entry.extent = 16;
    concrete = (target_ulong)fixture.target.raw;
    memcpy(source.value, &concrete, sizeof(concrete));
    queue = g_queue_new();
    CHECK(add_pointer_typed_candidate(
              queue, &source, &fixture.cell, &fixture.target, true,
              SNAPSHOT_POINTER_FROM_ACCESS),
          "OOB delta overflow falls back generically");
    CHECK(g_queue_get_length(queue) == 1 &&
          ((SnapshotMutationPlan *)g_queue_peek_head(queue))->mods[0].kind ==
              SNAPSHOT_MUTATION_POINTER_NULL,
          "OOB overflow publishes no partial typed prefix");
    free_plan_queue(queue);

    memset(source.value, 0, sizeof(source.value));
    fixture.entry.extent = 13;
    bool saw_success = false;
    for (int64_t fail_after = 0; fail_after < 32; fail_after++) {
        queue = g_queue_new();
        snapshot_mutation_test_set_alloc_fail_after(-1);
        SnapshotMutationPlan *sentinel = snapshot_mutation_new(
            &source, SNAPSHOT_MUTATION_BYTES, source.value, source.size,
            0, NULL);
        CHECK(sentinel != NULL &&
              snapshot_mutation_enqueue_one(queue, sentinel),
              "typed allocation sweep sentinel queues");
        snapshot_mutation_test_set_alloc_fail_after(fail_after);
        bool queued = add_pointer_typed_candidate(
            queue, &source, &fixture.cell, NULL, true,
            SNAPSHOT_POINTER_FROM_ACCESS);
        snapshot_mutation_test_set_alloc_fail_after(-1);
        if (queued) {
            CHECK(g_queue_get_length(queue) == 4,
                  "typed allocation sweep publishes the complete batch");
            saw_success = true;
            free_plan_queue(queue);
            break;
        }
        CHECK(g_queue_get_length(queue) == 1,
              "typed allocation failure publishes no partial batch");
        free_plan_queue(queue);
    }
    CHECK(saw_success, "typed allocation sweep reaches complete success");

    mutation_typed_fixture_free(&fixture);
}

static bool reference_variant_matches_write(
    const Stage7ReferenceVariant *expected,
    const SnapshotMutationWrite *actual)
{
    if (expected == NULL || actual == NULL ||
        (uint32_t)actual->kind != (uint32_t)expected->kind ||
        actual->addr != expected->addr || actual->size != expected->size ||
        actual->expr_index != expected->expr_index ||
        memcmp(actual->value, expected->value, sizeof(actual->value)) != 0 ||
        actual->target.extent != expected->target_extent ||
        actual->target.resolved_raw != expected->resolved_target_raw ||
        actual->target.resolved_end != expected->resolved_target_end) {
        return false;
    }
    if (expected->kind == STAGE7_REFERENCE_POINTER_FRESH) {
        return actual->target.bytes != NULL &&
               expected->target_bytes != NULL &&
               memcmp(actual->target.bytes, expected->target_bytes,
                      (size_t)expected->target_extent) == 0;
    }
    return actual->target.bytes == NULL;
}

static void test_reference_plan_matrix(void)
{
    MutationTypedFixture fixture;
    Stage7ReferenceCandidate reference_candidate;
    MutationCandidate source;
    target_ulong concrete;

    mutation_typed_fixture_init(&fixture, 13);
    memset(&source, 0, sizeof(source));
    source.addr = fixture.cell.start.raw;
    source.size = sizeof(target_ulong);
    source.expr = (Expr *)(uintptr_t)0x7654;
    memset(&reference_candidate, 0, sizeof(reference_candidate));
    reference_candidate.addr = source.addr;
    reference_candidate.size = source.size;
    reference_candidate.expr_index = -1;

#define CHECK_PLAN(_label, _allowed, _source_kind, _target) do {             \
        Stage7ReferencePlan expected = {0};                                  \
        GQueue *actual_queue = g_queue_new();                                \
        reference_candidate.addr = source.addr;                              \
        reference_candidate.size = source.size;                              \
        memcpy(reference_candidate.value, source.value,                    \
               sizeof(reference_candidate.value));                           \
        bool reference_ok = stage7_reference_plan_build(                     \
            fixture.ctx, &fixture.model, &reference_candidate,               \
            &fixture.cell, (_target), (_allowed),                              \
            (Stage7ReferencePointerSource)(_source_kind),                    \
            SNAPSHOT_PAGE_SIZE, 0x10, &expected);                              \
        bool production_ok = add_pointer_typed_candidate(                    \
            actual_queue, &source, &fixture.cell, (_target), (_allowed),       \
            (_source_kind));                                                   \
        CHECK(reference_ok && production_ok, _label " plan builds");          \
        if (reference_ok && production_ok) {                                   \
            CHECK(g_queue_get_length(actual_queue) == expected.count,          \
                  _label " variant count matches reference");                \
            if (g_queue_get_length(actual_queue) == expected.count) {          \
                for (uint32_t vi = 0; vi < expected.count; vi++) {             \
                    SnapshotMutationPlan *m = g_queue_peek_nth(actual_queue, vi);     \
                    CHECK(m != NULL && m->num_mods == 1 &&                     \
                          reference_variant_matches_write(                    \
                              &expected.variants[vi], &m->mods[0]),            \
                          _label " variant matches reference");              \
                }                                                               \
            }                                                                   \
        }                                                                       \
        stage7_reference_plan_clear(&expected);                                \
        free_plan_queue(actual_queue);                                          \
    } while (0)

    /* NULL pointer from both record families must produce the same three
     * independent fresh plans and exact full-target payloads. */
    memset(source.value, 0, sizeof(source.value));
    CHECK_PLAN("null primitive", true, SNAPSHOT_POINTER_FROM_PRIMITIVE,
               NULL);
    CHECK_PLAN("null pointer-access", true, SNAPSHOT_POINTER_FROM_ACCESS,
               NULL);

    /* A concrete target must produce NULL then checked OOB in the same
     * order, with the resolved baseline interval retained for observation. */
    concrete = fixture.target.raw;
    memcpy(source.value, &concrete, sizeof(concrete));
    CHECK_PLAN("non-null pointer-access", true, SNAPSHOT_POINTER_FROM_ACCESS,
               &fixture.target);

    /* The parent-wide sticky gate and every identity mismatch are per-access
     * generic fallbacks, never partial typed prefixes. */
    memset(source.value, 0, sizeof(source.value));
    CHECK_PLAN("sticky primitive fallback", false,
               SNAPSHOT_POINTER_FROM_PRIMITIVE, NULL);
    CHECK_PLAN("sticky pointer fallback", false,
               SNAPSHOT_POINTER_FROM_ACCESS, NULL);
    MutationCandidate saved_source = source;
    source.addr++;
    CHECK_PLAN("cell-address mismatch fallback", true,
               SNAPSHOT_POINTER_FROM_ACCESS, NULL);
    source = saved_source;

    OspreyRuntimeAddressRef stale = fixture.target;
    stale.prov_generation++;
    concrete = fixture.target.raw;
    memcpy(source.value, &concrete, sizeof(concrete));
    CHECK_PLAN("stale target fallback", true, SNAPSHOT_POINTER_FROM_ACCESS,
               &stale);
    OspreyRuntimeAddressRef wrong_region = fixture.target;
    wrong_region.address.region = fixture.global_region;
    CHECK_PLAN("canonical target mismatch fallback", true,
               SNAPSHOT_POINTER_FROM_ACCESS, &wrong_region);
    CHECK_PLAN("missing target locator fallback", true,
               SNAPSHOT_POINTER_FROM_ACCESS, NULL);

    /* Fresh-target size boundaries are compared at the exact cap and one
     * byte above it; changing the model cannot alter the source candidate. */
    memset(source.value, 0, sizeof(source.value));
    fixture.entry.extent = SNAPSHOT_PAGE_SIZE;
    CHECK_PLAN("fresh exact-cap", true, SNAPSHOT_POINTER_FROM_PRIMITIVE,
               NULL);
    fixture.entry.extent = SNAPSHOT_PAGE_SIZE + 1;
    CHECK_PLAN("fresh over-cap fallback", true,
               SNAPSHOT_POINTER_FROM_PRIMITIVE, NULL);
    fixture.entry.extent = 0;
    CHECK_PLAN("fresh zero-size fallback", true,
               SNAPSHOT_POINTER_FROM_PRIMITIVE, NULL);
    fixture.entry.extent = 13;

#undef CHECK_PLAN
    mutation_typed_fixture_free(&fixture);
}

static void test_fresh_pointer_application(void)
{
    CPUArchState *env = g_malloc0(sizeof(*env));
    MutationCandidate source;
    uint8_t payload[13];
    memset(&source, 0, sizeof(source));
    memset(payload, 0x5a, sizeof(payload));
    source.addr = TEST_GUEST_BASE + 0xb100;
    source.size = sizeof(target_ulong);
    source.expr = (Expr *)(uintptr_t)0x9876;
    target_ulong target = TEST_GUEST_BASE + 0xc000;
    memset(g2h(source.addr), 0xcc, sizeof(target_ulong));
    memset(g2h(target), 0xa5, sizeof(payload) + 1);

    SnapshotMutationPlan *plan = snapshot_mutation_new(
        &source, SNAPSHOT_MUTATION_POINTER_FRESH, source.value, source.size,
        sizeof(payload), payload);
    CHECK(plan != NULL, "fresh application plan allocates");
    if (plan != NULL) {
        uint8_t value_before[sizeof(plan->mods[0].value)];
        uint8_t payload_before[sizeof(payload)];
        memcpy(value_before, plan->mods[0].value, sizeof(value_before));
        memcpy(payload_before, plan->mods[0].target.bytes,
               sizeof(payload_before));
        test_mmap_result = (abi_long)target;
        test_mmap_length = 0;
        test_mmap_calls = 0;
        mod_manager = g_new0(ModificationManager, 1);
        mod_manager->modifications = g_queue_new();
        mod_manager->current = plan;
        mutation_analysis_started = true;
        snapshot_modify_memory(env);

        target_ulong applied = 0;
        memcpy(&applied, g2h(source.addr), sizeof(applied));
        CHECK(test_mmap_calls == 1 && test_mmap_length == sizeof(payload),
              "fresh mapping requests the exact decoded extent");
        CHECK(bytes_equal_value(g2h(target), sizeof(payload), 0x5a) &&
              ((uint8_t *)g2h(target))[sizeof(payload)] == 0xa5,
              "fresh application initializes exactly the owned extent");
        CHECK(applied == target,
              "fresh application publishes the mapped pointer cell");
        CHECK(memcmp(plan->mods[0].value, value_before,
                     sizeof(value_before)) == 0 &&
              memcmp(plan->mods[0].target.bytes, payload_before,
                     sizeof(payload_before)) == 0,
              "fresh application leaves the parent plan immutable");
        snapshot_modification_manager_reset(false);
    }

    void *shared = mmap(NULL, SNAPSHOT_PAGE_SIZE,
                        PROT_READ | PROT_WRITE,
                        MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    CHECK(shared != MAP_FAILED, "shared failure probe maps");
    if (shared != MAP_FAILED) {
        unsigned long saved_guest_base = guest_base;
        target_ulong cell = TEST_GUEST_BASE + 0x100;
        guest_base = (unsigned long)shared - TEST_GUEST_BASE;
        target_ulong sentinel = 0x1122334455667788ULL;
        memcpy(g2h(cell), &sentinel, sizeof(sentinel));
        source.addr = cell;
        plan = snapshot_mutation_new(
            &source, SNAPSHOT_MUTATION_POINTER_FRESH, source.value,
            source.size, sizeof(payload), payload);
        CHECK(plan != NULL, "fresh failure plan allocates");
        if (plan != NULL) {
            mod_manager = g_new0(ModificationManager, 1);
            mod_manager->modifications = g_queue_new();
            mod_manager->current = plan;
            mutation_analysis_started = true;
            test_mmap_result = -1;
            pid_t pid = fork();
            if (pid == 0) {
                if (g_osprey_ctx != NULL) {
                    osprey_free(g_osprey_ctx);
                    g_osprey_ctx = NULL;
                }
                snapshot_modify_memory(env);
                _exit(0);
            }
            int status = 0;
            CHECK(pid > 0 && waitpid(pid, &status, 0) == pid &&
                  WIFEXITED(status) && WEXITSTATUS(status) == 1,
                  "fresh mapping failure terminates the child");
            target_ulong after = 0;
            memcpy(&after, g2h(cell), sizeof(after));
            CHECK(after == sentinel,
                  "fresh mapping failure leaves the pointer cell unchanged");
            snapshot_modification_manager_reset(false);
        }
        guest_base = saved_guest_base;
        munmap(shared, SNAPSHOT_PAGE_SIZE);
    }
    test_mmap_result = -1;
    g_free(env);
}

static void test_atomic_plan_enqueue_failures(void)
{
    bool saw_success = false;
    MutationCandidate source;
    memset(&source, 0x5a, sizeof(source));
    source.addr = TEST_GUEST_BASE + 0xac00;
    source.size = sizeof(target_ulong);
    source.expr = (Expr *)(uintptr_t)0x9abc;

    for (int64_t fail_after = 0; fail_after < 64; fail_after++) {
        GQueue *queue = g_queue_new();
        snapshot_mutation_test_set_alloc_fail_after(-1);
        SnapshotMutationPlan *sentinel = snapshot_mutation_new(
            &source, SNAPSHOT_MUTATION_BYTES, source.value, source.size,
            0, NULL);
        CHECK(sentinel != NULL, "sentinel plan allocates");
        CHECK(snapshot_mutation_enqueue_one(queue, sentinel),
              "sentinel plan enqueues");
        MutationCandidate before = source;

        snapshot_mutation_test_set_alloc_fail_after(fail_after);
        bool queued = add_modification_primitive(queue, &source);
        snapshot_mutation_test_set_alloc_fail_after(-1);
        if (queued) {
            CHECK(g_queue_get_length(queue) == 4,
                  "successful batch appends all plans");
            CHECK(memcmp(&source, &before, sizeof(source)) == 0,
                  "successful batch leaves source unchanged");
            saw_success = true;
            free_plan_queue(queue);
            break;
        }
        CHECK(g_queue_get_length(queue) == 1,
              "failed batch leaves queue byte-count unchanged");
        CHECK(memcmp(&source, &before, sizeof(source)) == 0,
              "failed batch leaves source unchanged");
        free_plan_queue(queue);
    }
    CHECK(saw_success, "allocation-failure sweep reaches queue success");
}

static void test_nested_payload_failures(void)
{
    bool saw_success = false;
    MutationCandidate source;
    memset(&source, 0, sizeof(source));
    source.addr = TEST_GUEST_BASE + 0xac80;
    source.size = sizeof(target_ulong);
    uint8_t zero[sizeof(target_ulong)] = {0};
    uint8_t ones[sizeof(target_ulong)];
    memset(ones, 1, sizeof(ones));

    for (int64_t fail_after = 0; fail_after < 32; fail_after++) {
        GQueue *queue = g_queue_new();
        snapshot_mutation_test_set_alloc_fail_after(-1);
        SnapshotMutationPlan *sentinel = snapshot_mutation_new(
            &source, SNAPSHOT_MUTATION_BYTES, source.value, source.size,
            0, NULL);
        CHECK(sentinel != NULL, "nested-failure sentinel allocates");
        CHECK(snapshot_mutation_enqueue_one(queue, sentinel),
              "nested-failure sentinel enqueues");

        SnapshotMutationPlan *batch[2] = {NULL, NULL};
        snapshot_mutation_test_set_alloc_fail_after(fail_after);
        batch[0] = snapshot_mutation_new(
            &source, SNAPSHOT_MUTATION_POINTER_FRESH, zero, source.size,
            sizeof(zero), zero);
        batch[1] = snapshot_mutation_new(
            &source, SNAPSHOT_MUTATION_POINTER_FRESH, zero, source.size,
            sizeof(ones), ones);
        bool queued = false;
        if (batch[0] != NULL && batch[1] != NULL) {
            queued = snapshot_mutation_enqueue_batch(queue, batch, 2);
        } else {
            snapshot_mutation_free_batch(batch, 2);
        }
        snapshot_mutation_test_set_alloc_fail_after(-1);

        if (queued) {
            CHECK(g_queue_get_length(queue) == 3,
                  "nested-failure success appends both plans");
            saw_success = true;
            free_plan_queue(queue);
            break;
        }
        CHECK(g_queue_get_length(queue) == 1,
              "nested-failure batch leaves queue unchanged");
        free_plan_queue(queue);
    }
    CHECK(saw_success, "nested allocation-failure sweep reaches success");
}

static void test_owned_plan_validation(void)
{
    MutationCandidate source = {0};
    source.addr = CPU_NB_REGS;
    source.size = sizeof(target_ulong);
    CHECK(snapshot_mutation_new(&source, SNAPSHOT_MUTATION_BYTES,
                                source.value, source.size, 0, NULL) == NULL,
          "invalid register selector is rejected");

    source.addr = TEST_GUEST_BASE + 0xacc0;
    CHECK(snapshot_mutation_new(&source, (SnapshotMutationKind)-1,
                                source.value, source.size, 0, NULL) == NULL,
          "invalid mutation kind is rejected");
    CHECK(snapshot_mutation_new(&source, SNAPSHOT_MUTATION_POINTER_NULL,
                                source.value, 4, 0, NULL) == NULL,
          "non-native pointer width is rejected");
}

static void test_mutation_coordinator_contract(void)
{
    SnapshotMutationBaseline baseline = {0};
    SnapshotMutationBaselineEntry entries[4] = {0};
    SnapshotMutationCoordinator coordinator = {0};
    SnapshotMutationProposalSink sink = {0};
    SnapshotMutationProposalWrite writes[2] = {0};
    SnapshotMutationProposalVariant variant = {0};
    SnapshotMutationProposalFamily family = {0};
    GQueue *queue = g_queue_new();

    baseline.run_epoch = 7;
    baseline.entry_count = G_N_ELEMENTS(entries);
    baseline.entries = entries;
    for (uint32_t i = 0; i < G_N_ELEMENTS(entries); i++) {
        entries[i].token.run_epoch = baseline.run_epoch;
        entries[i].token.source_ordinal = i;
        entries[i].lane = i == 0 ? SNAPSHOT_MUTATION_LANE_PRIMITIVE
                                 : SNAPSHOT_MUTATION_LANE_ARGUMENT;
        entries[i].source_kind = i == 0
            ? SNAPSHOT_MUTATION_SOURCE_PRIMITIVE
            : SNAPSHOT_MUTATION_SOURCE_ARGUMENT_PRIMITIVE;
        entries[i].eligible = true;
        entries[i].typed_eligible = true;
        entries[i].size = i == 0 ? 1 : sizeof(target_ulong);
        entries[i].addr = i == 0 ? TEST_GUEST_BASE + 0xd000 : R_EAX;
        entries[i].planner_bytes[0] = (uint8_t)(0x10 + i);
    }
    entries[0].observed_read_valid = true;
    entries[0].access_id = 19;
    entries[0].pc = 0x400200;
    entries[0].observed_read_bytes[0] = 0x10;
    entries[3].addr = TEST_GUEST_BASE + 0xd000;
    entries[3].size = 2;

    coordinator.baseline = &baseline;
    coordinator.families = g_ptr_array_new_with_free_func(
        snapshot_mutation_proposal_family_free);
    coordinator.staged = g_ptr_array_new_with_free_func(
        (GDestroyNotify)snapshot_mutation_free);
    sink.coordinator = &coordinator;
    sink.advisor_id = 7;
    sink.advisor_priority = 2;

    writes[0].destination = entries[0].token;
    writes[0].kind = SNAPSHOT_MUTATION_BYTES;
    writes[0].size = 1;
    writes[0].value[0] = 0x22;
    writes[1].destination = entries[1].token;
    writes[1].kind = SNAPSHOT_MUTATION_BYTES;
    writes[1].size = sizeof(target_ulong);
    writes[1].value[0] = 0x44;
    variant.variant_id = 4;
    variant.write_count = G_N_ELEMENTS(writes);
    variant.writes = writes;
    family.advisor_id = sink.advisor_id;
    family.advisor_priority = sink.advisor_priority;
    family.family_id = 100;
    family.primary_seed = entries[0].token;
    family.seed_semantics = SNAPSHOT_MUTATION_SEED_SNAPSHOT_STATE;
    family.variant_count = 1;
    family.variants = &variant;

    CHECK(snapshot_mutation_sink_submit(&sink, &family),
          "coordinator accepts a complete family");
    CHECK(snapshot_mutation_sink_submit(&sink, &family) &&
              coordinator.families->len == 1,
          "coordinator deduplicates same-advisor descriptor");

    writes[0].value[0] = entries[0].planner_bytes[0];
    CHECK(!snapshot_mutation_proposal_validate(&coordinator, &family),
          "coordinator rejects an unchanged primary");
    writes[0].value[0] = 0x22;
    family.primary_seed.run_epoch++;
    CHECK(!snapshot_mutation_proposal_validate(&coordinator, &family),
          "coordinator rejects a stale source epoch");
    family.primary_seed.run_epoch = baseline.run_epoch;

    writes[0].kind = SNAPSHOT_MUTATION_POINTER_FRESH;
    writes[0].target_extent = 1;
    writes[0].target_bytes = NULL;
    CHECK(!snapshot_mutation_proposal_validate(&coordinator, &family),
          "coordinator rejects malformed fresh payload");
    writes[0].kind = SNAPSHOT_MUTATION_BYTES;
    writes[0].target_extent = 0;

    SnapshotMutationProposalWrite duplicate_register_writes[2] = {0};
    SnapshotMutationProposalVariant duplicate_register_variant = {0};
    SnapshotMutationProposalFamily duplicate_register_family = family;
    duplicate_register_writes[0].destination = entries[1].token;
    duplicate_register_writes[0].kind = SNAPSHOT_MUTATION_BYTES;
    duplicate_register_writes[0].size = sizeof(target_ulong);
    duplicate_register_writes[0].value[0] = 0x55;
    duplicate_register_writes[1] = duplicate_register_writes[0];
    duplicate_register_writes[1].destination = entries[2].token;
    duplicate_register_writes[1].value[0] = 0x66;
    duplicate_register_variant.variant_id = 1;
    duplicate_register_variant.write_count = 2;
    duplicate_register_variant.writes = duplicate_register_writes;
    duplicate_register_family.family_id = 101;
    duplicate_register_family.primary_seed = entries[1].token;
    duplicate_register_family.variants = &duplicate_register_variant;
    CHECK(!snapshot_mutation_proposal_validate(
              &coordinator, &duplicate_register_family),
          "coordinator rejects duplicate register writes");

    SnapshotMutationProposalWrite overlap_writes[2] = {0};
    SnapshotMutationProposalVariant overlap_variant = {0};
    SnapshotMutationProposalFamily overlap_family = family;
    overlap_writes[0] = writes[0];
    overlap_writes[0].destination = entries[0].token;
    overlap_writes[0].size = 1;
    overlap_writes[0].value[0] = 0x23;
    overlap_writes[1] = writes[0];
    overlap_writes[1].destination = entries[3].token;
    overlap_writes[1].size = 2;
    overlap_writes[1].value[0] = 0x24;
    overlap_variant.variant_id = 2;
    overlap_variant.write_count = 2;
    overlap_variant.writes = overlap_writes;
    overlap_family.family_id = 102;
    overlap_family.variants = &overlap_variant;
    CHECK(!snapshot_mutation_proposal_validate(&coordinator,
                                               &overlap_family),
          "coordinator rejects overlapping memory writes");

    SnapshotMutationProposalFamily *accepted =
        g_ptr_array_index(coordinator.families, 0);
    CHECK(snapshot_mutation_stage_family(&coordinator, accepted),
          "coordinator stages a complete family off-queue");
    CHECK(g_queue_is_empty(queue),
          "coordinator staging does not publish a queue prefix");
    CHECK(snapshot_mutation_coordinator_publish(&coordinator, queue) &&
              g_queue_get_length(queue) == 1,
          "coordinator publishes one owned plan per variant");
    if (g_queue_get_length(queue) == 1) {
        SnapshotMutationPlan *staged = g_queue_peek_head(queue);
        CHECK(staged->num_mods == 2 &&
                  staged->mods[0].addr == entries[0].addr &&
                  staged->mods[0].size == 1 &&
                  staged->mods[0].value[0] == 0x22 &&
                  staged->mods[1].addr == entries[1].addr &&
                  staged->mods[1].size == sizeof(target_ulong) &&
                  staged->mods[1].value[0] == 0x44,
              "staged plan carries the complete ordered write set");
        CHECK(staged->source_valid && staged->source_epoch == baseline.run_epoch &&
                  staged->source_ordinal == 0 &&
                  staged->source_kind == SNAPSHOT_MUTATION_SOURCE_PRIMITIVE &&
                  staged->seed_semantics ==
                      SNAPSHOT_MUTATION_SEED_SNAPSHOT_STATE &&
                  staged->family_valid && staged->family_id == family.family_id &&
                  staged->source_retained,
              "specialized plan owns validated primary source metadata");
        CHECK(staged->read_witness_applicable &&
                  staged->read_witness.valid &&
                  staged->read_witness.baseline_epoch == baseline.run_epoch &&
                  staged->read_witness.lane ==
                      SNAPSHOT_MUTATION_LANE_PRIMITIVE &&
                  staged->read_witness.access_id == entries[0].access_id &&
                  staged->read_witness.pc == entries[0].pc &&
                  staged->read_witness.addr == entries[0].addr &&
                  staged->read_witness.width == 1 &&
                  staged->read_witness.expected_bytes[0] == 0x22,
              "specialized scalar witness owns baseline identity and patch value");
    }
    free_plan_queue(queue);
    queue = g_queue_new();
    CHECK(snapshot_mutation_stage_generic(&coordinator, &entries[3]) &&
              snapshot_mutation_coordinator_publish(&coordinator, queue) &&
              g_queue_get_length(queue) == 3,
          "generic source plans publish as a complete batch");
    if (!g_queue_is_empty(queue)) {
        SnapshotMutationPlan *generic = g_queue_peek_head(queue);
        CHECK(generic->source_valid &&
                  generic->source_epoch == baseline.run_epoch &&
                  generic->source_ordinal == 3 &&
                  generic->source_ordinal != 0 &&
                  generic->source_kind ==
                      SNAPSHOT_MUTATION_SOURCE_ARGUMENT_PRIMITIVE &&
                  generic->seed_semantics ==
                      SNAPSHOT_MUTATION_SEED_SNAPSHOT_STATE &&
                  !generic->family_valid && !generic->source_retained,
              "generic plan does not fabricate source ordinal zero");
    }
    free_plan_queue(queue);
    snapshot_mutation_coordinator_clear(&coordinator);
}

static void test_manager_fifo_and_cleanup(void)
{
    reset_shared_records();
    SnapshotExitInfo exit_info = {0};
    mod_manager_init(&exit_info);
    CHECK(mod_manager != NULL && mutation_analysis_started,
          "manager initialization owns analysis state");

    MutationCandidate source = {0};
    source.addr = TEST_GUEST_BASE + 0xace0;
    source.size = sizeof(target_ulong);
    SnapshotMutationPlan *batch[3] = {NULL, NULL, NULL};
    for (uint32_t i = 0; i < G_N_ELEMENTS(batch); i++) {
        source.value[0] = (uint8_t)(0x11 * (i + 1));
        batch[i] = snapshot_mutation_new(
            &source, SNAPSHOT_MUTATION_BYTES, source.value, source.size,
            0, NULL);
    }
    CHECK(snapshot_mutation_enqueue_batch(mod_manager->modifications,
                                          batch, G_N_ELEMENTS(batch)),
          "manager FIFO batch queued");

    for (uint32_t i = 0; i < 3; i++) {
        int remaining = select_next_modification(&exit_info);
        CHECK(mod_manager != NULL && mod_manager->current != NULL &&
              mod_manager->current->mods[0].value[0] ==
                  (uint8_t)(0x11 * (i + 1)),
              "manager selects plans in FIFO order");
        CHECK(remaining == (int)(3 - i),
              "manager reports current plus queued count");
    }
    CHECK(select_next_modification(&exit_info) == 0,
          "manager reports exhausted queue");
    CHECK(mod_manager == NULL && mutation_analysis_started,
          "exhaustion destroys manager without reopening analysis");
    CHECK(select_next_modification(&exit_info) == 0,
          "exhausted manager remains terminal");
    snapshot_modification_manager_reset(false);

    for (uint32_t iteration = 0; iteration < 32; iteration++) {
        mod_manager_init(&exit_info);
        source.value[0] = (uint8_t)iteration;
        mod_manager->current = snapshot_mutation_new(
            &source, SNAPSHOT_MUTATION_BYTES, source.value, source.size,
            0, NULL);
        SnapshotMutationPlan *queued = snapshot_mutation_new(
            &source, SNAPSHOT_MUTATION_BYTES, source.value, source.size,
            0, NULL);
        CHECK(mod_manager->current != NULL && queued != NULL &&
              snapshot_mutation_enqueue_one(mod_manager->modifications,
                                            queued),
              "manager cleanup cycle owns current and queued plans");
        snapshot_modification_manager_reset(false);
        CHECK(mod_manager == NULL && !mutation_analysis_started,
              "manager cleanup cycle releases all ownership");
    }
}

static SnapshotMutationPlan *make_two_write_plan(
    target_ulong first_addr, uint32_t first_size, uint8_t first_value,
    target_ulong second_addr, uint32_t second_size, uint8_t second_value)
{
    SnapshotMutationPlan *plan = g_malloc0(sizeof(*plan));
    plan->num_mods = 2;
    plan->mods = g_malloc0(2 * sizeof(*plan->mods));
    plan->mods[0].kind = SNAPSHOT_MUTATION_BYTES;
    plan->mods[0].addr = first_addr;
    plan->mods[0].size = first_size;
    plan->mods[0].value[0] = first_value;
    plan->mods[1].kind = SNAPSHOT_MUTATION_BYTES;
    plan->mods[1].addr = second_addr;
    plan->mods[1].size = second_size;
    plan->mods[1].value[0] = second_value;
    return plan;
}

static void test_child_multiwrite_atomicity(void)
{
    CPUArchState *env = g_malloc0(sizeof(*env));
    void *shared = mmap(NULL, SNAPSHOT_PAGE_SIZE,
                        PROT_READ | PROT_WRITE,
                        MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    unsigned long saved_guest_base;
    target_ulong first = TEST_GUEST_BASE + 0x120;
    target_ulong second = TEST_GUEST_BASE + 0x128;
    int status = 0;

    CHECK(shared != MAP_FAILED, "multiwrite fixture maps shared memory");
    if (shared == MAP_FAILED) {
        g_free(env);
        return;
    }
    saved_guest_base = guest_base;
    guest_base = (unsigned long)shared - TEST_GUEST_BASE;
    memset(shared, 0xa5, SNAPSHOT_PAGE_SIZE);

    mod_manager = g_new0(ModificationManager, 1);
    mod_manager->modifications = g_queue_new();
    mod_manager->current = make_two_write_plan(first, 1, 0x11,
                                                second, 2, 0x22);
    mutation_analysis_started = true;
    pid_t pid = fork();
    if (pid == 0) {
        snapshot_modify_memory(env);
        _exit(0);
    }
    CHECK(pid > 0 && waitpid(pid, &status, 0) == pid &&
              WIFEXITED(status) && WEXITSTATUS(status) == 0,
          "valid multiwrite child resumes after complete preflight");
    CHECK(((uint8_t *)shared)[0x120] == 0x11 &&
              ((uint8_t *)shared)[0x128] == 0x22,
          "valid multiwrite publishes every cell");
    snapshot_modification_manager_reset(false);

    memset(shared, 0xa5, SNAPSHOT_PAGE_SIZE);
    mod_manager = g_new0(ModificationManager, 1);
    mod_manager->modifications = g_queue_new();
    mod_manager->current = make_two_write_plan(first, 2, 0x11,
                                                first + 1, 1, 0x22);
    mutation_analysis_started = true;
    status = 0;
    pid = fork();
    if (pid == 0) {
        snapshot_modify_memory(env);
        _exit(0);
    }
    CHECK(pid > 0 && waitpid(pid, &status, 0) == pid &&
              WIFEXITED(status) && WEXITSTATUS(status) == 1,
          "overlapping multiwrite exits before publication");
    CHECK(((uint8_t *)shared)[0x120] == 0xa5 &&
              ((uint8_t *)shared)[0x121] == 0xa5,
          "overlap rejection leaves every cell unchanged");
    snapshot_modification_manager_reset(false);

    guest_base = saved_guest_base;
    munmap(shared, SNAPSHOT_PAGE_SIZE);
    g_free(env);
}

static void test_variant_multiwrite_child_observation(void)
{
    /* One proposal variant with two writes must reach exactly one
     * disposable child that observes both cells together.  A descriptor
     * count alone would not prove the atomicity B0 now guarantees. */
    SnapshotMutationBaseline baseline = {0};
    SnapshotMutationBaselineEntry entries[2] = {0};
    SnapshotMutationCoordinator coordinator = {0};
    SnapshotMutationProposalSink sink = {0};
    SnapshotMutationProposalWrite writes[2] = {0};
    SnapshotMutationProposalVariant variant = {0};
    SnapshotMutationProposalFamily family = {0};
    GQueue *queue = g_queue_new();
    CPUArchState *env = g_malloc0(sizeof(*env));
    void *shared = mmap(NULL, SNAPSHOT_PAGE_SIZE,
                        PROT_READ | PROT_WRITE,
                        MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    unsigned long saved_guest_base = guest_base;
    target_ulong first = TEST_GUEST_BASE + 0x130;
    target_ulong second = TEST_GUEST_BASE + 0x138;
    int status = 0;

    CHECK(shared != MAP_FAILED, "variant fixture maps shared memory");
    if (shared == MAP_FAILED || queue == NULL || env == NULL) {
        g_free(env);
        g_free(queue);
        return;
    }
    guest_base = (unsigned long)shared - TEST_GUEST_BASE;
    memset(shared, 0xa5, SNAPSHOT_PAGE_SIZE);

    baseline.run_epoch = 11;
    baseline.entry_count = G_N_ELEMENTS(entries);
    baseline.entries = entries;
    for (uint32_t i = 0; i < G_N_ELEMENTS(entries); i++) {
        entries[i].token.run_epoch = baseline.run_epoch;
        entries[i].token.source_ordinal = i;
        entries[i].lane = SNAPSHOT_MUTATION_LANE_PRIMITIVE;
        entries[i].source_kind = SNAPSHOT_MUTATION_SOURCE_PRIMITIVE;
        entries[i].eligible = true;
        entries[i].typed_eligible = true;
        entries[i].size = 1;
        entries[i].addr = i == 0 ? first : second;
        entries[i].planner_bytes[0] = 0xa5;
    }
    entries[1].size = 2;

    writes[0].destination = entries[0].token;
    writes[0].kind = SNAPSHOT_MUTATION_BYTES;
    writes[0].size = 1;
    writes[0].value[0] = 0x11;
    writes[1].destination = entries[1].token;
    writes[1].kind = SNAPSHOT_MUTATION_BYTES;
    writes[1].size = 2;
    writes[1].value[0] = 0x22;
    writes[1].value[1] = 0x77;
    variant.variant_id = 3;
    variant.write_count = G_N_ELEMENTS(writes);
    variant.writes = writes;
    family.advisor_id = sink.advisor_id = 2;
    family.advisor_priority = sink.advisor_priority = 1;
    family.family_id = 7;
    family.primary_seed = entries[0].token;
    family.seed_semantics = SNAPSHOT_MUTATION_SEED_SNAPSHOT_STATE;
    family.variant_count = 1;
    family.variants = &variant;

    coordinator.baseline = &baseline;
    coordinator.families = g_ptr_array_new_with_free_func(
        snapshot_mutation_proposal_family_free);
    coordinator.staged = g_ptr_array_new_with_free_func(
        (GDestroyNotify)snapshot_mutation_free);
    sink.coordinator = &coordinator;

    CHECK(snapshot_mutation_sink_submit(&sink, &family),
          "variant multiwrite family is accepted");
    CHECK(snapshot_mutation_stage_family(
              &coordinator, g_ptr_array_index(coordinator.families, 0)) &&
              coordinator.staged->len == 1,
          "one variant stages exactly one plan");
    CHECK(snapshot_mutation_coordinator_publish(&coordinator, queue) &&
              g_queue_get_length(queue) == 1,
          "one variant publishes exactly one queue entry");

    mod_manager = g_new0(ModificationManager, 1);
    mod_manager->modifications = queue;
    mod_manager->current = g_queue_pop_head(queue);
    mutation_analysis_started = true;
    CHECK(mod_manager->current != NULL &&
              mod_manager->current->num_mods == 2,
          "published plan carries both writes");
    pid_t pid = fork();
    if (pid == 0) {
        snapshot_modify_memory(env);
        _exit(0);
    }
    CHECK(pid > 0 && waitpid(pid, &status, 0) == pid &&
              WIFEXITED(status) && WEXITSTATUS(status) == 0,
          "variant multiwrite child resumes after complete preflight");
    CHECK(((uint8_t *)shared)[0x130] == 0x11 &&
              ((uint8_t *)shared)[0x138] == 0x22 &&
              ((uint8_t *)shared)[0x139] == 0x77,
          "variant multiwrite child observes both writes together");

    snapshot_modification_manager_reset(false);
    guest_base = saved_guest_base;
    munmap(shared, SNAPSHOT_PAGE_SIZE);
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    g_free(env);
}

static void test_child_application_does_not_mutate_plan(void)
{
    reset_shared_records();
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    MutationCandidate source;
    memset(&source, 0, sizeof(source));
    source.addr = TEST_GUEST_BASE + 0xad00;
    source.size = sizeof(target_ulong);
    source.expr = (Expr *)(uintptr_t)0xdef0;
    target_ulong value = 0x1122334455667788ULL;
    memcpy(source.value, &value, sizeof(value));

    SnapshotMutationPlan *plan = snapshot_mutation_new(
        &source, SNAPSHOT_MUTATION_BYTES, source.value, source.size, 0, NULL);
    CHECK(plan != NULL, "application plan allocates");
    if (plan != NULL) {
        uint8_t before[sizeof(plan->mods[0].value)];
        memcpy(before, plan->mods[0].value, sizeof(before));
        mod_manager = g_new0(ModificationManager, 1);
        mod_manager->modifications = g_queue_new();
        mod_manager->current = plan;
        snapshot_modify_memory(env);
        CHECK(memcmp(plan->mods[0].value, before, sizeof(before)) == 0,
              "child application preserves queued plan bytes");
        target_ulong applied = 0;
        memcpy(&applied, g2h(source.addr), sizeof(applied));
        CHECK(applied == value, "child application writes private value");
        snapshot_modification_manager_reset(false);
    }

    memset(&source, 0, sizeof(source));
    source.addr = R_EAX;
    source.size = sizeof(target_ulong);
    value = 0x8877665544332211ULL;
    memcpy(source.value, &value, sizeof(value));
    plan = snapshot_mutation_new(
        &source, SNAPSHOT_MUTATION_BYTES, source.value, source.size, 0, NULL);
    CHECK(plan != NULL, "register application plan allocates");
    if (plan != NULL) {
        uint8_t before[sizeof(plan->mods[0].value)];
        memcpy(before, plan->mods[0].value, sizeof(before));
        mod_manager = g_new0(ModificationManager, 1);
        mod_manager->modifications = g_queue_new();
        mod_manager->current = plan;
        mutation_analysis_started = true;
        snapshot_modify_memory(env);
        CHECK(env->regs[R_EAX] == value,
              "register destination uses the legacy selector contract");
        CHECK(memcmp(plan->mods[0].value, before, sizeof(before)) == 0,
              "register application preserves queued plan bytes");
        snapshot_modification_manager_reset(false);
    }
    g_free(env);
}

static void test_invalid_patch_result(void)
{
    int fds[2];
    int status = pipe(fds);
    CHECK(status == 0, "create patch-result stream");
    if (status != 0) return;
    const char row[] = "[patch] [id 1] [br 1] [v 1]\n";
    CHECK(write(fds[1], row, sizeof(row) - 1) == sizeof(row) - 1,
          "write out-of-range patch result");
    close(fds[1]);

    pid_t pid = fork();
    if (pid == 0) {
        uint32_t iteration = 1;
        BinradarManager manager = {0};
        manager.cur_iter = &iteration;
        manager.patch_fd_r = fds[0];
        manager.current = binradar_cache_new_iteration(&manager);
        manager.patch_result_parser = sbsv_parser_new(SBSV_PARSER_DEFAULT);
        if (sbsv_parser_add_schema(manager.patch_result_parser,
                "[patch] [id: int] [br: int] [v: int]") != SBSV_OK) {
            _exit(2);
        }
        binradar_cache_drain_patch(&manager);
        _exit(0);
    }
    close(fds[0]);
    status = 0;
    CHECK(pid > 0 && waitpid(pid, &status, 0) == pid &&
              WIFEXITED(status) && WEXITSTATUS(status) == 1,
          "out-of-range patch result is fatal rather than silently discarded");
}

static void test_cached_feedback_writer(void)
{
    GError *error = NULL;
    char *directory = g_dir_make_tmp("binradar-feedback-test-XXXXXX", &error);
    CHECK(directory != NULL && error == NULL,
          "feedback writer creates temporary directory");
    if (directory == NULL) {
        if (error != NULL) g_error_free(error);
        return;
    }

    BinradarManager manager = {0};
    manager.patch_max_id = 3;
    manager.current = binradar_cache_new_iteration(&manager);
    manager.feedback_dir = directory;
    manager.poc_fault_valid = true;
    manager.poc_fault_source = SNAPSHOT_FAULT_REFERENCE_GUEST_SIGNAL;
    manager.poc_fault_addr = 0x1234;
    manager.cache_bytes = g_byte_array_new();
    const uint8_t snapshot[] = {'B', 'R', 'C', 'H'};
    g_byte_array_append(manager.cache_bytes, snapshot, sizeof(snapshot));

    GArray *branches = g_array_new(FALSE, FALSE, sizeof(int));
    int branch = 0;
    g_array_append_val(branches, branch);
    branch = 1;
    g_array_append_val(branches, branch);

    SnapshotMutationWrite writes[2] = {0};
    writes[0].kind = SNAPSHOT_MUTATION_BYTES;
    writes[0].addr = 0x4000;
    writes[0].size = 2;
    writes[0].value[0] = 0xaa;
    writes[0].value[1] = 0xbb;
    writes[1].kind = SNAPSHOT_MUTATION_POINTER_OOB;
    writes[1].addr = 0x4008;
    writes[1].size = sizeof(target_ulong);
    writes[1].value[0] = 0xcc;
    writes[1].value[1] = 0xdd;
    const BinradarMutationFeedbackView mutation = {
        .writes = writes,
        .write_count = G_N_ELEMENTS(writes),
    };

    const char *expected_results[] = {"benign", "ignored", "malicious"};
    const bool crashes[] = {false, true, true};
    const target_ulong faults[] = {0, 0x5678, 0x1234};
    for (uint32_t patch = 1; patch <= 3; patch++) {
        PatchedResult *result = &manager.current->patch_results[patch];
        result->patch_id = patch;
        result->representative = patch;
        result->is_crash = crashes[patch - 1];
        result->fault_reference_valid = result->is_crash;
        result->fault_reference_source = result->is_crash
            ? SNAPSHOT_FAULT_REFERENCE_GUEST_SIGNAL
            : SNAPSHOT_FAULT_REFERENCE_UNAVAILABLE;
        result->fault_loc = faults[patch - 1];
        CHECK(binradar_cache_feedback_write(
                  &manager, 2, patch, branches, &mutation),
              "feedback writer stages representative pair");
        CHECK(binradar_cache_feedback_publish(&manager),
              "staged feedback pair publishes completely");

        char *metadata_name = g_strdup_printf(
            "iteration-00000002-patch-%08u.sbsv", patch);
        char *metadata_path = g_build_filename(directory, metadata_name, NULL);
        char *metadata = NULL;
        gsize metadata_size = 0;
        CHECK(g_file_get_contents(metadata_path, &metadata, &metadata_size,
                                  NULL),
              "feedback metadata is readable");
        if (metadata != NULL) {
            char *classification = g_strdup_printf("[result %s]",
                                                    expected_results[patch - 1]);
            CHECK(strstr(metadata, classification) != NULL,
                  "feedback classification matches POC fault location");
            CHECK(strstr(metadata, "[branches 0,1]") != NULL &&
                  strstr(metadata, "[mutation-writes 2]") != NULL &&
                  strstr(metadata, "[index 0] [kind bytes]") != NULL &&
                  strstr(metadata, "[value aabb]") != NULL &&
                  strstr(metadata, "[index 1] [kind pointer-oob]") != NULL &&
                  strstr(metadata, "[value ccdd000000000000]") != NULL,
                  "feedback metadata records every ordered plan write");
            if (patch == 3) {
                sbsv_parser *parser = sbsv_parser_new(SBSV_PARSER_DEFAULT);
                CHECK(sbsv_parser_add_schema(parser,
                    "[binradar-feedback] [version: int] [iteration: int] "
                    "[patch: int] [snapshot-file: str] "
                    "[snapshot-count: int] [branches: str] [outcome: str] "
                    "[fault-addr: str] [fault-valid: bool] "
                    "[fault-source: str] [poc-fault-addr: str] "
                    "[poc-fault-valid: bool] [poc-fault-source: str] "
                    "[same-fault: bool] [result: str] "
                    "[mutation-writes: int]") == SBSV_OK &&
                    sbsv_parser_add_schema(parser,
                    "[binradar-mutation] [index: int] "
                    "[kind: str] [addr: str] [size: int] [value: str] "
                    "[target-extent: int]") == SBSV_OK &&
                    sbsv_parser_loads(parser, metadata) == SBSV_OK,
                    "feedback metadata is valid SBSV");
                const sbsv_row **rows = NULL;
                size_t row_count = 0;
                CHECK(sbsv_parser_get_rows(parser, "binradar-feedback",
                                           &rows, &row_count) == SBSV_OK &&
                      row_count == 1,
                      "feedback metadata has one run row");
                sbsv_free_row_ref_array(rows);
                rows = NULL;
                row_count = 0;
                CHECK(sbsv_parser_get_rows(parser,
                                           "binradar-mutation",
                                           &rows, &row_count) == SBSV_OK &&
                      row_count == 2,
                      "feedback metadata has one row per plan write");
                sbsv_free_row_ref_array(rows);
                sbsv_parser_free(parser);
            }
            g_free(classification);
        }
        g_free(metadata);
        g_free(metadata_path);
        g_free(metadata_name);
    }

    /* An explicitly valid PC-zero reference must classify as malicious;
     * making the POC reference unavailable must instead ignore the same
     * numeric crash address. */
    {
        PatchedResult *zero = &manager.current->patch_results[3];
        char *zero_name;
        char *zero_path;
        char *zero_snapshot;
        char *zero_metadata = NULL;
        gsize zero_metadata_size = 0;
        zero->is_crash = true;
        zero->fault_reference_valid = true;
        zero->fault_reference_source = SNAPSHOT_FAULT_REFERENCE_GUEST_SIGNAL;
        zero->fault_loc = 0;
        manager.poc_fault_valid = true;
        manager.poc_fault_source = SNAPSHOT_FAULT_REFERENCE_GUEST_SIGNAL;
        manager.poc_fault_addr = 0;
        CHECK(binradar_cache_feedback_write(
                  &manager, 3, 3, branches, &mutation),
              "feedback writer stages an explicitly valid PC-zero crash");
        CHECK(binradar_cache_feedback_publish(&manager),
              "staged feedback pair publishes completely");
        zero_name = g_strdup("iteration-00000003-patch-00000003.sbsv");
        zero_path = g_build_filename(directory, zero_name, NULL);
        CHECK(g_file_get_contents(zero_path, &zero_metadata,
                                  &zero_metadata_size, NULL) &&
              strstr(zero_metadata, "[result malicious]") != NULL,
              "valid PC-zero reference remains malicious");
        g_free(zero_metadata);
        zero_metadata = NULL;
        zero_snapshot = g_strdup("iteration-00000003-patch-00000003.brch");
        {
            char *snapshot_file = g_build_filename(directory, zero_snapshot,
                                                   NULL);
            unlink(snapshot_file);
            g_free(snapshot_file);
        }
        g_free(zero_snapshot);
        unlink(zero_path);
        g_free(zero_path);
        g_free(zero_name);
        manager.poc_fault_valid = false;
        manager.poc_fault_source = SNAPSHOT_FAULT_REFERENCE_UNAVAILABLE;
        CHECK(binradar_cache_feedback_write(
                  &manager, 4, 3, branches, &mutation),
              "feedback writer stages unavailable POC reference");
        CHECK(binradar_cache_feedback_publish(&manager),
              "staged feedback pair publishes completely");
        zero_name = g_strdup("iteration-00000004-patch-00000003.sbsv");
        zero_path = g_build_filename(directory, zero_name, NULL);
        CHECK(g_file_get_contents(zero_path, &zero_metadata,
                                  &zero_metadata_size, NULL) &&
              strstr(zero_metadata, "[result ignored]") != NULL,
              "unavailable POC reference ignores crash feedback");
        g_free(zero_metadata);
        unlink(zero_path);
        zero_snapshot = g_strdup("iteration-00000004-patch-00000003.brch");
        {
            char *snapshot_file = g_build_filename(directory, zero_snapshot,
                                                   NULL);
            unlink(snapshot_file);
            g_free(snapshot_file);
        }
        g_free(zero_snapshot);
        g_free(zero_path);
        g_free(zero_name);
    }

    /* A forkserver child may exit during mutation validation, before guest
     * execution.  Its inherited manager must not remove the parent's staged
     * pair. */
    {
        BinradarManager *saved_manager = binradar_manager;
        char *staged_path;
        int status = 0;
        CHECK(binradar_cache_feedback_write(
                  &manager, 5, 1, branches, &mutation),
              "child-cleanup fixture stages a complete pair");
        staged_path = g_build_filename(
            manager.feedback_staging_dir,
            "iteration-00000005-patch-00000001.brch", NULL);
        binradar_manager = &manager;
        pid_t pid = fork();
        if (pid == 0) {
            afl_fork_child = 1;
            exit_with_status(1);
        }
        CHECK(pid > 0 && waitpid(pid, &status, 0) == pid &&
                  WIFEXITED(status) && WEXITSTATUS(status) == 1,
              "forkserver child exits through manager-aware cleanup");
        binradar_manager = saved_manager;
        CHECK(g_file_test(staged_path, G_FILE_TEST_EXISTS),
              "forkserver child preserves the parent's staged pair");
        binradar_cache_feedback_drop(&manager);
        CHECK(manager.feedback_staging_dir == NULL,
              "parent drop removes child-preserved staging");
        g_free(staged_path);
    }

    /* A second-file collision must not leave the first half of a pair in the
     * committed directory.  This exercises rollback after the BRCH rename has
     * already succeeded. */
    {
        char *blocked_path = g_build_filename(
            directory, "iteration-00000005-patch-00000001.sbsv", NULL);
        char *rolled_back_path = g_build_filename(
            directory, "iteration-00000005-patch-00000001.brch", NULL);
        CHECK(g_mkdir(blocked_path, 0700) == 0,
              "feedback rollback fixture creates destination collision");
        CHECK(binradar_cache_feedback_write(
                  &manager, 5, 1, branches, &mutation),
              "feedback rollback fixture stages a complete pair");
        CHECK(!binradar_cache_feedback_publish(&manager),
              "feedback publication reports a second-file failure");
        CHECK(!g_file_test(rolled_back_path, G_FILE_TEST_EXISTS),
              "feedback publication rolls back the first renamed file");
        CHECK(manager.feedback_staging_dir == NULL,
              "feedback failure removes the attempt staging directory");
        rmdir(blocked_path);
        g_free(rolled_back_path);
        g_free(blocked_path);
    }

    char *snapshot_path = g_build_filename(
        directory, "iteration-00000002-patch-00000003.brch", NULL);
    char *snapshot_data = NULL;
    gsize snapshot_size = 0;
    CHECK(g_file_get_contents(snapshot_path, &snapshot_data, &snapshot_size,
                              NULL) &&
          snapshot_size == sizeof(snapshot) &&
          memcmp(snapshot_data, snapshot, sizeof(snapshot)) == 0,
          "feedback snapshot preserves validated BRCH bytes");
    g_free(snapshot_data);
    g_free(snapshot_path);

    for (uint32_t patch = 1; patch <= 3; patch++) {
        char *stem = g_strdup_printf(
            "iteration-00000002-patch-%08u", patch);
        char *name = g_strconcat(stem, ".brch", NULL);
        char *path = g_build_filename(directory, name, NULL);
        unlink(path);
        g_free(path);
        g_free(name);
        name = g_strconcat(stem, ".sbsv", NULL);
        path = g_build_filename(directory, name, NULL);
        unlink(path);
        g_free(path);
        g_free(name);
        g_free(stem);
    }
    binradar_cache_feedback_release(&manager);
    rmdir(directory);
    g_array_free(branches, TRUE);
    g_byte_array_free(manager.cache_bytes, TRUE);
    g_free(manager.current->patch_results);
    g_free(manager.current);
    g_free(directory);
}

/* ------------------------------------------------------------------ */
/* Entry                                                               */
/* ------------------------------------------------------------------ */

/* ------------------------------------------------------------------ */
/* Symbolic boundary advisor (Package 2)                               */
/* ------------------------------------------------------------------ */

/* Build a frozen arena and baseline that the advisor can traverse.  Nodes are
 * appended in index order and every operand points backwards, exactly like the
 * real pools.  The caller owns arena/query arrays and the baseline entries. */
typedef struct SymbolicFixture {
    Expr arena[64];
    uint32_t arena_len;
    Query queries[16];
    uint32_t query_len;
    SnapshotMutationBaseline baseline;
    SnapshotMutationBaselineEntry entries[8];
    uint32_t entry_count;
} SymbolicFixture;

static void fixture_arena(Expr *node, uint8_t opkind, Expr *op1,
                          bool op1_const, uint64_t op1_value, Expr *op2,
                          bool op2_const, uint64_t op2_value)
{
    memset(node, 0, sizeof(*node));
    node->opkind = opkind;
    node->op1_is_const = op1_const ? 1 : 0;
    node->op2_is_const = op2_const ? 1 : 0;
    node->op1 = op1_const ? (Expr *)(uintptr_t)op1_value : op1;
    node->op2 = op2_const ? (Expr *)(uintptr_t)op2_value : op2;
}

static uint32_t fixture_push(SymbolicFixture *fx, uint8_t opkind, Expr *op1,
                             bool op1_const, uint64_t op1_value, Expr *op2,
                             bool op2_const, uint64_t op2_value)
{
    uint32_t index = fx->arena_len++;
    fixture_arena(&fx->arena[index], opkind, op1, op1_const, op1_value, op2,
                  op2_const, op2_value);
    return index;
}

static uint32_t fixture_leaf(SymbolicFixture *fx)
{
    uint32_t index = fx->arena_len++;
    memset(&fx->arena[index], 0, sizeof(fx->arena[index]));
    fx->arena[index].opkind = IS_SYMBOLIC;
    return index;
}

static void fixture_branch(SymbolicFixture *fx, uint8_t opkind, Expr *op1,
                           bool op1_const, uint64_t op1_value, Expr *op2,
                           bool op2_const, uint64_t op2_value, uint64_t width)
{
    uint32_t index;
    Query *query;
    memset(&fx->queries[fx->query_len], 0, sizeof(fx->queries[0]));
    index = fixture_push(fx, opkind, op1, op1_const, op1_value, op2, op2_const,
                         op2_value);
    fx->arena[index].op3 = (Expr *)(uintptr_t)width;
    query = &fx->queries[fx->query_len++];
    query->query = &fx->arena[index];
}

/* One primitive source at `cell` with `observed` bytes loaded 4 bytes wide. */
static void fixture_source(SymbolicFixture *fx, uintptr_t cell,
                           uint32_t observed, uint32_t root_index,
                           int64_t query_index)
{
    SnapshotMutationBaselineEntry *entry = &fx->entries[fx->entry_count];
    memset(entry, 0, sizeof(*entry));
    entry->token.run_epoch = 11;
    entry->token.source_ordinal = fx->entry_count;
    entry->lane = SNAPSHOT_MUTATION_LANE_PRIMITIVE;
    entry->source_kind = SNAPSHOT_MUTATION_SOURCE_PRIMITIVE;
    entry->eligible = true;
    entry->typed_eligible = true;
    entry->addr = cell;
    entry->size = 4;
    entry->observed_read_valid = true;
    memcpy(entry->observed_read_bytes, &observed, sizeof(observed));
    memcpy(entry->planner_bytes, &observed, sizeof(observed));
    entry->expr_index = root_index;
    entry->query_index = query_index;
    entry->root_extension = SNAPSHOT_ROOT_ZEXT;
    fx->entry_count++;
}

/* Bind a source's load root the way a real child suffix does: an admitted
 * `BINRADAR_CONCRETIZATION` wrapper whose copied address, width, and bytes
 * match the retained record.  The advisor traces a branch back to a memory
 * cell only through this evidence, because the retained per-address record
 * keeps just the last load of that address. */
static void fixture_bind(SymbolicFixture *fx, uint32_t root_index,
                         uintptr_t cell, uint32_t observed)
{
    uint32_t index = fixture_push(fx, BINRADAR_CONCRETIZATION,
                                  &fx->arena[root_index], false, 0, NULL, true,
                                  0);
    Query *query;

    memcpy(&fx->arena[index].op2, &observed, sizeof(observed));
    fx->arena[index].op2_is_const = 1;
    fx->arena[index].op3 = (Expr *)(uintptr_t)4;
    fx->arena[index].op3_is_const = 1;
    query = &fx->queries[fx->query_len++];
    query->query = &fx->arena[index];
    query->address = cell;
}

static void fixture_init(SymbolicFixture *fx)
{
    memset(fx, 0, sizeof(*fx));
    fx->baseline.run_epoch = 11;
    fx->baseline.counts_valid = true;
    fx->baseline.entries = fx->entries;
}

static void fixture_seal(SymbolicFixture *fx, uint64_t expr_entry,
                         uint64_t query_entry)
{
    fx->baseline.entry_count = fx->entry_count;
    fx->baseline.expr_start = (int64_t)expr_entry;
    fx->baseline.expr_end = (int64_t)fx->arena_len;
    fx->baseline.query_start = (int64_t)query_entry;
    fx->baseline.query_end = (int64_t)fx->query_len;
}

/* Run the advisor in boundary mode against the fixture and return accepted
 * families.  Configuration is process-global, so this forces the mode and
 * restores OFF afterwards to keep later groups deterministic. */
static void symbolic_configure(SnapshotSymbolicMode mode)
{
    static bool forced = false;
    if (!forced) {
        snapshot_symbolic_configure();
        forced = true;
    }
    s_symbolic_config.mode = mode;
    s_symbolic_config.valid = true;
}

static uint32_t symbolic_run_fixture(SymbolicFixture *fx,
                                     SnapshotMutationCoordinator *coordinator,
                                     SnapshotMutationProposalSink *sink)
{
    SnapshotSymbolicView view;
    memset(&view, 0, sizeof(view));
    view.expr_base = fx->arena;
    view.query_base = fx->queries;
    view.expr_entry = fx->baseline.expr_start;
    view.expr_exit = fx->baseline.expr_end;
    view.query_entry = fx->baseline.query_start;
    view.query_exit = fx->baseline.query_end;
    view.baseline = &fx->baseline;
    view.run_epoch = fx->baseline.run_epoch;
    sink->coordinator = coordinator;
    sink->advisor_id = SNAPSHOT_SYMBOLIC_ADVISOR_ID;
    sink->advisor_priority = SNAPSHOT_SYMBOLIC_ADVISOR_PRIORITY;
    return snapshot_symbolic_run(&view, sink);
}

static SnapshotMutationCoordinator fixture_coordinator(SymbolicFixture *fx)
{
    SnapshotMutationCoordinator coordinator;
    memset(&coordinator, 0, sizeof(coordinator));
    coordinator.baseline = &fx->baseline;
    coordinator.families = g_ptr_array_new_with_free_func(
        snapshot_mutation_proposal_family_free);
    coordinator.staged = g_ptr_array_new_with_free_func(
        (GDestroyNotify)snapshot_mutation_free);
    return coordinator;
}

/* Canonical textual dump of every staged plan descriptor.  Used to prove that
 * a mode which must not change the queue leaves it byte-identical. */
static GString *dump_staged_plans(const SnapshotMutationCoordinator *coordinator)
{
    GString *out = g_string_new(NULL);

    for (guint i = 0; i < coordinator->staged->len; i++) {
        const SnapshotMutationPlan *plan =
            g_ptr_array_index(coordinator->staged, i);
        g_string_append_printf(out,
                               "plan[%u] mods=%u advisor=%u ordinal=%u "
                               "family=%llu\n",
                               i, plan->num_mods, plan->advisor_id,
                               plan->source_ordinal,
                               (unsigned long long)plan->family_id);
        for (uint32_t m = 0; m < plan->num_mods; m++) {
            const SnapshotMutationWrite *mod = &plan->mods[m];
            g_string_append_printf(out,
                                   "  mod[%u] addr=%llx size=%u kind=%u "
                                   "value=",
                                   m, (unsigned long long)mod->addr,
                                   mod->size, (uint32_t)mod->kind);
            for (size_t b = 0; b < sizeof(mod->value); b++) {
                g_string_append_printf(out, "%02x", mod->value[b]);
            }
            g_string_append_printf(out,
                                   " target-raw=%llx target-end=%llx "
                                   "extent=%llu\n",
                                   (unsigned long long)mod->target.resolved_raw,
                                   (unsigned long long)mod->target.resolved_end,
                                   (unsigned long long)mod->target.extent);
        }
    }
    return out;
}

/* Package 4: the feedback sidecar must describe the plan the boundary advisor
 * actually applied, and the child must have observed the same value.  This
 * links three independently-produced artifacts -- the advisor's family, the
 * owned plan the child applied, and the version-2 sidecar bytes -- instead of
 * asserting each one separately. */
static void test_symbolic_feedback_matches_applied_plan(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe600;
    uint32_t leaf, zext;
    uint32_t proposed = 0;
    GError *error = NULL;
    char *directory;
    BinradarManager manager = {0};
    char *metadata_path = NULL;
    char *metadata = NULL;
    gsize metadata_size = 0;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    zext = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    fixture_source(&fx, cell, 0x0010, (int64_t)zext, 0);
    fixture_bind(&fx, zext, cell, 0x0010);
    fixture_branch(&fx, LTU, &fx.arena[zext], false, 0, NULL, true, 0x1000, 8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 1 &&
              coordinator.families->len == 1,
          "advisor proposes one family for the feedback cross-check");
    if (coordinator.families->len != 1) {
        g_ptr_array_free(coordinator.families, TRUE);
        g_ptr_array_free(coordinator.staged, TRUE);
        symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
        return;
    }
    CHECK(snapshot_mutation_stage_family(
              &coordinator, g_ptr_array_index(coordinator.families, 0)) &&
              coordinator.staged->len ==
                  ((SnapshotMutationProposalFamily *)g_ptr_array_index(
                      coordinator.families, 0))->variant_count,
          "advisor family stages every bounded variant as one owned plan");
    memcpy(&proposed,
           ((SnapshotMutationPlan *)g_ptr_array_index(
                coordinator.staged, 0))->mods[0].value,
           sizeof(proposed));
    CHECK(proposed == 0x1000,
          "applied plan carries the synthesized boundary value");

    /* Feed the owned plan to the production writer as the child's mutation
     * plan, exactly as the forkserver parent does before a mutation child. */
    directory = g_dir_make_tmp("binradar-symbolic-feedback-XXXXXX", &error);
    CHECK(directory != NULL && error == NULL,
          "symbolic feedback fixture creates a temporary directory");
    if (directory != NULL) {
        const uint8_t snapshot[] = {'B', 'R', 'C', 'H'};
        GArray *branches = g_array_new(FALSE, FALSE, sizeof(int));
        int branch = 1;

        manager.patch_max_id = 2;
        manager.current = binradar_cache_new_iteration(&manager);
        manager.feedback_dir = directory;
        manager.poc_fault_valid = true;
        manager.poc_fault_source = SNAPSHOT_FAULT_REFERENCE_GUEST_SIGNAL;
        manager.poc_fault_addr = 0x1234;
        manager.cache_bytes = g_byte_array_new();
        g_byte_array_append(manager.cache_bytes, snapshot, sizeof(snapshot));
        g_array_append_val(branches, branch);
        for (uint32_t patch = 1; patch <= 2; patch++) {
            PatchedResult *result = &manager.current->patch_results[patch];
            result->patch_id = patch;
            result->representative = patch;
            result->is_crash = patch == 2;
            result->fault_reference_valid = result->is_crash;
            result->fault_reference_source = result->is_crash
                ? SNAPSHOT_FAULT_REFERENCE_GUEST_SIGNAL
                : SNAPSHOT_FAULT_REFERENCE_UNAVAILABLE;
            result->fault_loc = patch == 2 ? 0x1234u : 0u;
        }
        const SnapshotMutationPlan *feedback_plan =
            g_ptr_array_index(coordinator.staged, 0);
        const BinradarMutationFeedbackView mutation = {
            .writes = feedback_plan->mods,
            .write_count = feedback_plan->num_mods,
        };
        CHECK(binradar_cache_feedback_write(
                  &manager, 4, 1, branches, &mutation),
              "feedback writer stages the representative child pair");
        {
            char *staged_pair = g_build_filename(
                directory, "iteration-00000004-patch-00000001.sbsv", NULL);
            CHECK(!g_file_test(staged_pair, G_FILE_TEST_EXISTS),
                  "a staged pair is not yet committed sweep evidence");
            g_free(staged_pair);
        }
        CHECK(binradar_cache_feedback_publish(&manager),
              "staged feedback pair publishes completely");

        metadata_path = g_build_filename(
            directory, "iteration-00000004-patch-00000001.sbsv", NULL);
        CHECK(g_file_get_contents(metadata_path, &metadata, &metadata_size,
                                  NULL),
              "symbolic feedback sidecar is readable");
        if (metadata != NULL) {
            sbsv_parser *parser = sbsv_parser_new(SBSV_PARSER_DEFAULT);
            const sbsv_row **rows = NULL;
            size_t row_count = 0;
            const char *recorded = NULL;
            CHECK(sbsv_parser_add_schema(parser,
                "[binradar-feedback] [version: int] [iteration: int] "
                "[patch: int] [snapshot-file: str] [snapshot-count: int] "
                "[branches: str] [outcome: str] [fault-addr: str] "
                "[fault-valid: bool] [fault-source: str] "
                "[poc-fault-addr: str] [poc-fault-valid: bool] "
                "[poc-fault-source: str] [same-fault: bool] "
                "[result: str] [mutation-writes: int]") == SBSV_OK &&
                sbsv_parser_add_schema(parser,
                "[binradar-mutation] [index: int] [kind: str] [addr: str] "
                "[size: int] [value: str] [target-extent: int]") == SBSV_OK &&
                sbsv_parser_loads(parser, metadata) == SBSV_OK,
                "symbolic feedback sidecar is valid version-2 SBSV");
            CHECK(sbsv_parser_get_rows(parser, "binradar-mutation",
                                       &rows, &row_count) == SBSV_OK &&
                      row_count == 1,
                  "symbolic sidecar records exactly the one applied write");
            if (row_count == 1) {
                for (size_t field = 0;
                     field < sbsv_row_field_count(rows[0]); field++) {
                    if (strcmp(sbsv_field_name(&rows[0]->fields[field]),
                               "value") == 0) {
                        recorded = rows[0]->fields[field].value.data.
                            string_value;
                    }
                }
                CHECK(recorded != NULL &&
                          strcmp(recorded, "00100000") == 0,
                      "sidecar write value is the little-endian plan bytes");
            }
            sbsv_free_row_ref_array(rows);
            rows = NULL;
            row_count = 0;
            CHECK(sbsv_parser_get_rows(parser, "binradar-feedback",
                                       &rows, &row_count) == SBSV_OK &&
                      row_count == 1,
                  "symbolic sidecar has exactly one run row");
            sbsv_free_row_ref_array(rows);
            sbsv_parser_free(parser);
        }
        g_free(metadata);
        metadata = NULL;

        /* Iteration 1 is the baseline: no pair, because no mutation child
         * ran.  The writer must refuse rather than stage a stale plan. */
            CHECK(binradar_cache_feedback_write(
                  &manager, 1, 1, branches, &mutation),
              "iteration 1 is a no-op for the feedback writer");
        {
            char *iter1 = g_build_filename(
                directory, "iteration-00000001-patch-00000001.sbsv", NULL);
            CHECK(!g_file_test(iter1, G_FILE_TEST_EXISTS),
                  "iteration 1 writes no feedback pair");
            g_free(iter1);
        }

        g_array_free(branches, TRUE);
        g_byte_array_free(manager.cache_bytes, TRUE);
        binradar_cache_feedback_release(&manager);
        binradar_cache_clear_iteration(&manager);
        g_free(manager.current->patch_results);
        g_free(manager.current);
        {
            char *pair = g_build_filename(
                directory, "iteration-00000004-patch-00000001.brch", NULL);
            unlink(pair);
            g_free(pair);
            pair = g_build_filename(
                directory, "iteration-00000001-patch-00000001.sbsv", NULL);
            unlink(pair);
            g_free(pair);
            pair = g_build_filename(
                directory, "iteration-00000001-patch-00000001.brch", NULL);
            unlink(pair);
            g_free(pair);
        }
        unlink(metadata_path);
        g_free(metadata_path);
        rmdir(directory);
        g_free(directory);
    }
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* The pair claims to describe one real child.  A member materialized from a
 * cached vector has no child of its own, so publication must be impossible for
 * it -- in both places that could produce one. */
static void test_feedback_requires_representative_child(void)
{
    GError *error = NULL;
    char *directory = g_dir_make_tmp("binradar-rep-feedback-XXXXXX", &error);
    BinradarManager manager = {0};
    GArray *branches = g_array_new(FALSE, FALSE, sizeof(int));
    char *pair_path = NULL;
    int branch = 1;

    CHECK(directory != NULL && error == NULL,
          "representative fixture creates a temporary directory");
    if (directory == NULL) {
        g_array_free(branches, TRUE);
        return;
    }
    manager.patch_max_id = 2;
    manager.current = binradar_cache_new_iteration(&manager);
    manager.feedback_dir = directory;
    manager.poc_fault_addr = 0x1234;
    manager.cache_bytes = g_byte_array_new();
    g_array_append_val(branches, branch);
    for (uint32_t patch = 1; patch <= 2; patch++) {
        PatchedResult *result = &manager.current->patch_results[patch];
        result->patch_id = patch;
        result->representative = patch;
        result->is_crash = false;
    }
    /* Materialize patch 2 from patch 1's cached vector exactly as the
     * forkserver parent does: same branch vector, representative = patch 1. */
    manager.current->patch_results[1].br_taken =
        g_array_sized_new(FALSE, FALSE, sizeof(int), branches->len);
    g_array_append_vals(manager.current->patch_results[1].br_taken,
                        branches->data, branches->len);
    const SnapshotExitInfo outcome = {.valid = 1};
    binradar_cache_materialize(&manager, 2, 1, branches, &outcome);
    CHECK(manager.current->patch_results[2].representative == 1,
          "cache hit records the representative that produced its vector");
    CHECK(binradar_cache_vectors_equal(
              manager.current->patch_results[2].br_taken, branches),
          "cache hit carries the representative's observed vector");

    /* The writer refuses a non-representative request outright: a cache hit
     * must never publish a sidecar pretending to be a real child. */
    CHECK(!binradar_cache_feedback_write(
              &manager, 4, 2, branches, NULL),
          "cache-materialized member is rejected by the feedback writer");
    pair_path = g_build_filename(
        directory, "iteration-00000004-patch-00000002.sbsv", NULL);
    CHECK(!g_file_test(pair_path, G_FILE_TEST_EXISTS),
          "cache-materialized member emits no feedback pair");
    g_free(pair_path);

    g_array_free(branches, TRUE);
    g_byte_array_free(manager.cache_bytes, TRUE);
    binradar_cache_feedback_release(&manager);
    binradar_cache_clear_iteration(&manager);
    g_free(manager.current->patch_results);
    g_free(manager.current);
    rmdir(directory);
    g_free(directory);
}

/* Malformed BRCH bytes must not be publishable.  The writer copies whatever
 * the capture holds, so the guard lives in the cache vector: a representative
 * whose captured snapshot cannot reproduce the observed branches disables
 * publication instead of emitting a pair no consumer can trust. */
static void test_feedback_rejects_malformed_brch(void)
{
    BinradarManager manager = {0};
    GArray *vector = NULL;
    const uint8_t truncated[] = {'B', 'R', 'C', 'H'};
    const uint8_t short_header[] = {0x42, 0x52, 0x43, 0x48, 0x01, 0x00};

    manager.cache_family = BRCACHE_FAMILY_GENERIC;
    manager.cache_bytes = g_byte_array_new();
    /* Fewer bytes than one header: the record walk must fail closed. */
    g_byte_array_append(manager.cache_bytes, truncated, sizeof(truncated));
    CHECK(!binradar_cache_vector(&manager, 1, 1, &vector) && vector == NULL,
          "a truncated snapshot stream rejects cache evaluation");
    g_byte_array_set_size(manager.cache_bytes, 0);
    g_byte_array_append(manager.cache_bytes, short_header,
                        sizeof(short_header));
    CHECK(!binradar_cache_vector(&manager, 1, 1, &vector) && vector == NULL,
          "a sub-header snapshot stream rejects cache evaluation");
    /* Wrong magic with a complete-looking header must also fail closed. */
    g_byte_array_set_size(manager.cache_bytes, 0);
    {
        BinradarSnapshotHeader header = {
            .magic = 0xdeadbeefu,
            .version = BRCACHE_SNAPSHOT_VERSION,
            .patch_id = 1,
            .branch = 0,
            .stack_size = 0,
            .flags = 0,
        };
        uint8_t zero_payload[16 * sizeof(uint64_t)] = {0};
        g_byte_array_append(manager.cache_bytes, (const uint8_t *)&header,
                            sizeof(header));
        g_byte_array_append(manager.cache_bytes, zero_payload,
                            sizeof(zero_payload));
    }
    CHECK(!binradar_cache_vector(&manager, 1, 1, &vector) && vector == NULL,
          "a bad-magic snapshot stream rejects cache evaluation");
    g_byte_array_free(manager.cache_bytes, TRUE);
}

/* The canonical case: a 4-byte symbolic read compared against a constant with
 * an unsigned less-than.  The advisor must propose exactly the constant, as a
 * single 4-byte OBSERVED_READ write, and nothing else. */
static void test_symbolic_boundary_unsigned(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe000;
    uint32_t leaf, zext;
    uint32_t accepted;
    uint32_t value = 0x0010;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    zext = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    fixture_source(&fx, cell, value, (int64_t)zext, 0);
    fixture_bind(&fx, zext, cell, value);
    /* if (v < 0x1000) */
    fixture_branch(&fx, LTU, &fx.arena[zext], false, 0, NULL, true, 0x1000, 8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    accepted = symbolic_run_fixture(&fx, &coordinator, &sink);
    CHECK(accepted == 1 && coordinator.families->len == 1,
          "advisor accepts exactly one boundary family");
    if (coordinator.families->len == 1) {
        const SnapshotMutationProposalFamily *family =
            g_ptr_array_index(coordinator.families, 0);
        const SnapshotMutationProposalWrite *write;
        uint32_t lowered = 0;
        CHECK(family->advisor_id == SNAPSHOT_SYMBOLIC_ADVISOR_ID &&
                  family->advisor_priority ==
                      SNAPSHOT_SYMBOLIC_ADVISOR_PRIORITY,
              "family carries the advisor identity and priority");
        CHECK(family->seed_semantics == SNAPSHOT_MUTATION_SEED_OBSERVED_READ &&
                  family->primary_seed.source_ordinal == 0,
              "family is an observed-read family for the source ordinal");
        CHECK(family->variant_count >= 1 && family->variant_count <= 3 &&
                  family->variants[0].write_count == 1,
              "bounded variants each carry one primary write");
        write = &family->variants[0].writes[0];
        memcpy(&lowered, write->value, sizeof(lowered));
        CHECK(write->kind == SNAPSHOT_MUTATION_BYTES && write->size == 4 &&
                  lowered == 0x1000,
              "proposed value is the comparison constant at the source width");
    }
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* The observed value already sits on the false side of the branch: no flip is
 * reachable at this width, so the advisor must abstain instead of proposing a
 * value that changes nothing. */
static void test_symbolic_no_false_side(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe100;
    uint32_t leaf, zext;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    zext = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    /* Observed 0x10: ">= 0" is satisfied for every representable value, so no
     * value at this width can make the branch false. */
    fixture_source(&fx, cell, 0x10, (int64_t)zext, 0);
    fixture_bind(&fx, zext, cell, 0x10);
    fixture_branch(&fx, GEU, &fx.arena[zext], false, 0, NULL, true, 0, 8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0 &&
              coordinator.families->len == 0,
          "advisor abstains when no false value exists at the width");
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* Arithmetic and masking chains must invert exactly.  v is read as 4 bytes and
 * the branch is ((v & 0xffff) + 0x100) == 0x1234.  The nearest value on the
 * false side of the equality is 0x1235, so the required operand is 0x1235 and
 * the source bytes are 0x1135. */
static void test_symbolic_transform_chain(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe200;
    uint32_t leaf, zext, and_node, add_node;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    zext = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    /* and_node = zext & 0xffff ; add_node = and_node + 0x100 */
    and_node = fixture_push(&fx, AND, &fx.arena[zext], false, 0, NULL, true,
                            0xffff);
    add_node = fixture_push(&fx, ADD, &fx.arena[and_node], false, 0, NULL, true,
                            0x100);
    /* The recorded predicate is the one the baseline satisfied, so the
     * observed bytes must themselves reach the equality: 0x1134 & 0xffff +
     * 0x100 == 0x1234. */
    fixture_source(&fx, cell, 0x1134, (int64_t)zext, 0);
    fixture_bind(&fx, zext, cell, 0x1134);
    fixture_branch(&fx, EQ, &fx.arena[add_node], false, 0, NULL, true, 0x1234,
                   8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 1,
          "advisor accepts an invertible and/add chain");
    if (coordinator.families->len == 1) {
        const SnapshotMutationProposalFamily *family =
            g_ptr_array_index(coordinator.families, 0);
        const SnapshotMutationProposalWrite *write =
            &family->variants[0].writes[0];
        uint32_t lowered = 0;
        memcpy(&lowered, write->value, sizeof(lowered));
        CHECK(lowered == 0x1135,
              "chain inversion recovers the required source bytes");
    }
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* A later extension must propagate a label from op1.  The encoded source
 * width lives in op2 and is not itself an expression operand. */
static void test_symbolic_nested_extension(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe280;
    uint32_t leaf, root, nested;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    root = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    nested = fixture_push(&fx, ZEXT, &fx.arena[root], false, 0,
                          (Expr *)(uintptr_t)32, false, 0);
    fixture_source(&fx, cell, 0x10, (int64_t)root, 0);
    fixture_bind(&fx, root, cell, 0x10);
    fixture_branch(&fx, LTU, &fx.arena[nested], false, 0, NULL, true, 0x1000,
                   8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 1,
          "label propagates through a non-root extension");
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* Forward verification must start from the lowered source, not from the
 * required comparison operand.  For 32-bit arithmetic, 0x101 + 0xffffffff is
 * 0x100.  The 0x101 false-side operand lowers to source 0x102 and must survive
 * verification even though reapplying the transform to operand 0x101 would
 * incorrectly reconstruct the original true value. */
static void test_symbolic_reevaluates_lowered_source(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe2a0;
    uint32_t leaf, root, add_node;
    bool found = false;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    root = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    add_node = fixture_push(&fx, ADD, &fx.arena[root], false, 0, NULL, true,
                            0xffffffffu);
    fx.arena[add_node].op3 = (Expr *)(uintptr_t)4;
    fx.arena[add_node].op3_is_const = 1;
    fixture_source(&fx, cell, 0x101, (int64_t)root, 0);
    fixture_bind(&fx, root, cell, 0x101);
    fixture_branch(&fx, EQ, &fx.arena[add_node], false, 0, NULL, true, 0x100,
                   4);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 1,
          "modular add candidate survives lowered-source reevaluation");
    if (coordinator.families->len == 1) {
        const SnapshotMutationProposalFamily *family =
            g_ptr_array_index(coordinator.families, 0);
        for (uint32_t i = 0; i < family->variant_count; i++) {
            uint32_t lowered = 0;
            memcpy(&lowered, family->variants[i].writes[0].value,
                   sizeof(lowered));
            if (lowered == 0x102) found = true;
        }
    }
    CHECK(found, "verified family retains the 0x102 lowered source value");
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* Repeated dynamic instances of one branch produce repeated query records.
 * They must not consume the three source slots with duplicate child plans. */
static void test_symbolic_candidate_deduplication(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe2c0;
    uint32_t leaf, root;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    root = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    fixture_source(&fx, cell, 0x10, (int64_t)root, 0);
    fixture_bind(&fx, root, cell, 0x10);
    for (uint32_t i = 0; i < 3; i++) {
        fixture_branch(&fx, LTU, &fx.arena[root], false, 0, NULL, true,
                       0x1000, 8);
    }
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 1,
          "repeated branch queries still produce one family");
    if (coordinator.families->len == 1) {
        const SnapshotMutationProposalFamily *family =
            g_ptr_array_index(coordinator.families, 0);
        uint32_t first = 0, second = 0;
        CHECK(family->variant_count == 2,
              "exact and adjacent values occupy two unique slots");
        if (family->variant_count >= 2) {
            memcpy(&first, family->variants[0].writes[0].value,
                   sizeof(first));
            memcpy(&second, family->variants[1].writes[0].value,
                   sizeof(second));
            CHECK(first == 0x1000 && second == 0x1001,
                  "deduplicated variants retain deterministic boundary order");
        }
    }
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* A masked operand can only ever hold bits inside its mask.  When the branch
 * boundary lies outside that image the advisor must abstain rather than
 * propose a value the guest can never reach: (v & 0xff) < 0x140 is satisfied
 * by the observed 0x40, but no masked value is >= 0x140. */
static void test_symbolic_mask_no_preimage(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe300;
    uint32_t leaf, zext, and_node;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    zext = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    and_node = fixture_push(&fx, AND, &fx.arena[zext], false, 0, NULL, true,
                            0x00ff);
    fixture_source(&fx, cell, 0x0040, (int64_t)zext, 0);
    fixture_bind(&fx, zext, cell, 0x0040);
    fixture_branch(&fx, LTU, &fx.arena[and_node], false, 0, NULL, true, 0x140,
                   8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0,
          "advisor abstains when the mask target has no preimage");
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* When the boundary does have a preimage the advisor must find it: with the
 * same mask, (v & 0xff) < 0x40 is satisfied by 0x40 and the opposite boundary
 * 0x40 is reachable, so the source becomes 0x40. */
static void test_symbolic_mask_preimage_found(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe380;
    uint32_t leaf, zext, and_node;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    zext = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    and_node = fixture_push(&fx, AND, &fx.arena[zext], false, 0, NULL, true,
                            0x00ff);
    fixture_source(&fx, cell, 0x0120, (int64_t)zext, 0);
    fixture_bind(&fx, zext, cell, 0x0120);
    fixture_branch(&fx, LTU, &fx.arena[and_node], false, 0, NULL, true, 0x40,
                   8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 1,
          "advisor finds a masked preimage when one exists");
    if (coordinator.families->len == 1) {
        const SnapshotMutationProposalFamily *family =
            g_ptr_array_index(coordinator.families, 0);
        const SnapshotMutationProposalWrite *write =
            &family->variants[0].writes[0];
        uint32_t lowered = 0;
        memcpy(&lowered, write->value, sizeof(lowered));
        CHECK((lowered & 0xff) == 0x40,
              "masked candidate takes the required low bits");
    }
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* Shadow mode must do all the analysis and submit nothing. */
static void test_symbolic_shadow_submits_nothing(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe400;
    uint32_t leaf, zext;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    zext = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    fixture_source(&fx, cell, 0x0010, (int64_t)zext, 0);
    fixture_bind(&fx, zext, cell, 0x0010);
    fixture_branch(&fx, LTU, &fx.arena[zext], false, 0, NULL, true, 0x1000, 8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_SHADOW);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0 &&
              coordinator.families->len == 0,
          "shadow mode never submits a family");
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* Off mode must not even traverse: no families and no state change. */
static void test_symbolic_off_is_inert(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe500;
    uint32_t leaf, zext;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    zext = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    fixture_source(&fx, cell, 0x0010, (int64_t)zext, 0);
    fixture_bind(&fx, zext, cell, 0x0010);
    fixture_branch(&fx, LTU, &fx.arena[zext], false, 0, NULL, true, 0x1000, 8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0 &&
              coordinator.families->len == 0,
          "off mode submits nothing");
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
}

/* The constant side may be the left operand.  The advisor must mirror the
 * operator before deriving the boundary: 0x1000 > v is v < 0x1000, so the
 * boundary is still exactly 0x1000. */
static void test_symbolic_mirrored_constant(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe600;
    uint32_t leaf, zext;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    zext = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    fixture_source(&fx, cell, 0x0010, (int64_t)zext, 0);
    fixture_bind(&fx, zext, cell, 0x0010);
    /* 0x1000 > v  <=>  v < 0x1000 */
    fixture_branch(&fx, GTU, NULL, true, 0x1000, &fx.arena[zext], false, 0, 8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 1,
          "advisor accepts a comparison with the constant on the left");
    if (coordinator.families->len == 1) {
        const SnapshotMutationProposalFamily *family =
            g_ptr_array_index(coordinator.families, 0);
        const SnapshotMutationProposalWrite *write =
            &family->variants[0].writes[0];
        uint32_t lowered = 0;
        memcpy(&lowered, write->value, sizeof(lowered));
        CHECK(lowered == 0x1000,
              "mirrored operator yields the same boundary value");
    }
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* A source whose retained read was never finalized (no observed bytes) must be
 * skipped even though its root and a matching branch exist. */
static void test_symbolic_unobserved_source_skipped(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe700;
    uint32_t leaf, zext;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    zext = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    fixture_source(&fx, cell, 0x0010, (int64_t)zext, 0);
    fx.entries[0].observed_read_valid = false;
    fixture_branch(&fx, LTU, &fx.arena[zext], false, 0, NULL, true, 0x1000, 8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0,
          "advisor skips a source without a finalized observation");
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* The work budget is a hard bound: a single unit of work cannot admit the
 * forward pass, so the advisor abstains without touching the sink. */
static void test_symbolic_work_budget_abstains(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe800;
    uint32_t leaf, zext;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    zext = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    fixture_source(&fx, cell, 0x0010, (int64_t)zext, 0);
    fixture_bind(&fx, zext, cell, 0x0010);
    fixture_branch(&fx, LTU, &fx.arena[zext], false, 0, NULL, true, 0x1000, 8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    s_symbolic_config.max_work = 1;
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0,
          "exhausted work budget abstains locally");
    s_symbolic_config.max_work = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_WORK;

    /* The same fixture with a restored budget still succeeds, proving the
     * abstention was the budget and not a traversal failure. */
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 1,
          "restored budget admits the same fixture");
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* The byte budget is reserved before every advisor-owned allocation.  A limit
 * below the fixed tables must abstain without allocating candidates or
 * publishing a family prefix. */
static void test_symbolic_byte_budget_abstains(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe880;
    uint32_t leaf, root;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    root = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    fixture_source(&fx, cell, 0x10, (int64_t)root, 0);
    fixture_bind(&fx, root, cell, 0x10);
    fixture_branch(&fx, LTU, &fx.arena[root], false, 0, NULL, true, 0x1000,
                   8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    s_symbolic_config.max_bytes = 1;
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0 &&
              coordinator.families->len == 0,
          "byte budget exhaustion publishes no family prefix");
    s_symbolic_config.max_bytes = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_BYTES;
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 1,
          "restored byte budget admits the same fixture");
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* A retained primitive record is keyed by address, so a later load of the same
 * bytes replaces the record and its finalized root.  The branch under analysis
 * may consume the *earlier* load's root, which then sits in the frozen prefix
 * and is unreachable from the replacement's root.  The advisor must still bind
 * that earlier root from the child suffix's concretization wrapper for the
 * record, which is the evidence that those bytes flowed through it.  Without
 * this, every real guest whose compared value is reloaded before the branch
 * silently abstains. */
static void test_symbolic_replaced_record_binds_alias(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xe900;
    uint32_t leaf, first_root, later_root;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    /* The load the branch consumes. */
    first_root = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true,
                              32);
    fixture_source(&fx, cell, 0x0010, (int64_t)first_root, 0);
    fixture_bind(&fx, first_root, cell, 0x0010);
    /* A later load of the same bytes: the record now points at this root, so a
     * naive seed would label only here and never reach the comparison. */
    later_root = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true,
                              32);
    fx.entries[0].expr_index = (int64_t)later_root;
    fixture_bind(&fx, later_root, cell, 0x0010);
    fixture_branch(&fx, LTU, &fx.arena[first_root], false, 0, NULL, true,
                   0x1000, 8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 1,
          "advisor binds the earlier load root of a replaced record");
    if (coordinator.families->len == 1) {
        const SnapshotMutationProposalFamily *family =
            g_ptr_array_index(coordinator.families, 0);
        const SnapshotMutationProposalWrite *write =
            &family->variants[0].writes[0];
        uint32_t lowered = 0;
        memcpy(&lowered, write->value, sizeof(lowered));
        CHECK(lowered == 0x1000 && write->size == 4,
              "aliased root still yields the boundary at the record width");
    }
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* A wrapper whose copied bytes or address disagree with every retained record
 * proves nothing about that record, so it must not bind a root. */
static void test_symbolic_mismatched_wrapper_not_bound(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xea00;
    uint32_t leaf, root;

    reset_runtime();
    fixture_init(&fx);
    leaf = fixture_leaf(&fx);
    root = fixture_push(&fx, ZEXT, &fx.arena[leaf], false, 0, NULL, true, 32);
    fixture_source(&fx, cell, 0x0010, (int64_t)root, 0);
    /* Same width, different bytes: the evidence does not describe this
     * record's value, so nothing may be proposed from it. */
    fixture_bind(&fx, root, cell, 0x0099);
    fixture_branch(&fx, LTU, &fx.arena[root], false, 0, NULL, true, 0x1000, 8);
    fixture_seal(&fx, 0, 0);

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0 &&
              coordinator.families->len == 0,
          "advisor ignores a wrapper that disagrees with the record bytes");
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* ------------------------------------------------------------------ */

/* Continuation policy (P2).  One unusable attempt must not end a healthy
 * queue, a long tail of ordinary mutation misses must not trip the failure
 * limit, and a discarded baseline is reported as baseline-unavailable. */
static void test_forkserver_continuation_policy(void)
{
    BinradarForkserverDriver driver = {0};
    /* A completed attempt with queued work keeps going and clears nothing. */
    CHECK(binradar_forkserver_stop_reason(
              &driver, BINRADAR_FORKSERVER_ATTEMPT_COMPLETED, false, false,
              false, false, 7) == BINRADAR_FORKSERVER_STOP_CONTINUE,
          "a committed attempt with queued plans continues");
    CHECK(driver.consecutive_bad_attempts == 0,
          "a committed attempt resets the bad-attempt counter");
    /* Unusable exits advance the counter but keep the sweep alive. */
    CHECK(binradar_forkserver_stop_reason(
              &driver, BINRADAR_FORKSERVER_ATTEMPT_UNUSABLE_EXIT, true, false,
              false, false, 6) == BINRADAR_FORKSERVER_STOP_CONTINUE,
          "one unusable exit does not end the sweep");
    CHECK(driver.consecutive_bad_attempts == 1,
          "an unusable exit advances the bad-attempt counter");
    /* Ordinary no-observation misses neither advance nor reset it, so a long
     * tail of mutation misses cannot stop a healthy queue. */
    for (uint32_t i = 0; i < 50; i++) {
        CHECK(binradar_forkserver_stop_reason(
                  &driver, BINRADAR_FORKSERVER_ATTEMPT_NO_OBSERVATION, true,
                  false, false, false, 6) == BINRADAR_FORKSERVER_STOP_CONTINUE,
              "a no-observation miss never stops the sweep");
    }
    CHECK(driver.consecutive_bad_attempts == 1,
          "no-observation misses leave the bad-attempt counter alone");
    /* The bounded limit is reached only by genuinely bad attempts. */
    driver.bad_attempt_limit = 3;
    CHECK(binradar_forkserver_stop_reason(
              &driver, BINRADAR_FORKSERVER_ATTEMPT_TIMEOUT, true, true, false,
              false, 5) == BINRADAR_FORKSERVER_STOP_CONTINUE,
          "the second bad attempt is still below the limit");
    CHECK(binradar_forkserver_stop_reason(
              &driver, BINRADAR_FORKSERVER_ATTEMPT_UNUSABLE_EXIT, true, false,
              false, false, 4) == BINRADAR_FORKSERVER_STOP_FAILURE_LIMIT,
          "the consecutive limit stops the sweep");
    /* A discarded baseline is its own terminal reason and reports no queue. */
    BinradarForkserverDriver fresh = {0};
    CHECK(binradar_forkserver_stop_reason(
              &fresh, BINRADAR_FORKSERVER_ATTEMPT_TIMEOUT, true, true, false,
              true, 0) == BINRADAR_FORKSERVER_STOP_BASELINE_UNAVAILABLE,
          "a discarded baseline reports baseline-unavailable");
    CHECK(binradar_forkserver_attempt_result_name(
              BINRADAR_FORKSERVER_ATTEMPT_NO_OBSERVATION) != NULL &&
          strcmp(binradar_forkserver_attempt_result_name(
                     BINRADAR_FORKSERVER_ATTEMPT_NO_OBSERVATION),
                 "no-observation") == 0,
          "attempt-result names are stable for logs");
    /* An engine failure outranks every other classification. */
    CHECK(binradar_forkserver_stop_reason(
              &fresh, BINRADAR_FORKSERVER_ATTEMPT_UNUSABLE_EXIT, true, false,
              true, false, 3) == BINRADAR_FORKSERVER_STOP_RESOURCE_FAILURE,
          "an unexplained engine death reports resource-failure");
}

/* ------------------------------------------------------------------ */
/* P4a: stage profile, stop attribution, completed-digest determinism  */
/* ------------------------------------------------------------------ */

/* Build the canonical unsigned fixture: one 4-byte retained read compared
 * against 0x1000 with LTU, observed on the true side. */
static void symbolic_canonical_fixture(SymbolicFixture *fx, uintptr_t cell)
{
    uint32_t leaf, zext;

    fixture_init(fx);
    leaf = fixture_leaf(fx);
    zext = fixture_push(fx, ZEXT, &fx->arena[leaf], false, 0, NULL, true, 32);
    fixture_source(fx, cell, 0x0010, (int64_t)zext, 0);
    fixture_bind(fx, zext, cell, 0x0010);
    fixture_branch(fx, LTU, &fx->arena[zext], false, 0, NULL, true, 0x1000, 8);
    fixture_seal(fx, 0, 0);
}

/* Direct tracer entry points use the same unsigned-decimal language as the
 * orchestrator.  Missing means default; an explicitly empty or signed value is
 * malformed rather than another spelling of a default or positive integer. */
static void test_symbolic_budget_parser_is_strict(void)
{
    const char *name = "BINRADAR_TEST_SYMBOLIC_BUDGET";
    uint64_t value = 99;

    g_unsetenv(name);
    CHECK(parse_u64_env(name, &value) && value == 99,
          "missing symbolic budget preserves the caller default");
    g_setenv(name, "", TRUE);
    CHECK(!parse_u64_env(name, &value),
          "empty symbolic budget is malformed");
    g_setenv(name, "+1", TRUE);
    CHECK(!parse_u64_env(name, &value),
          "positive sign is outside the unsigned-decimal grammar");
    g_setenv(name, " 1", TRUE);
    CHECK(!parse_u64_env(name, &value),
          "budget whitespace is outside the unsigned-decimal grammar");
    g_setenv(name, "18446744073709551615", TRUE);
    CHECK(parse_u64_env(name, &value) && value == UINT64_MAX,
          "maximum uint64 symbolic budget parses exactly");
    g_setenv(name, "18446744073709551616", TRUE);
    CHECK(!parse_u64_env(name, &value),
          "overflowing symbolic budget is malformed");
    g_unsetenv(name);
}

/* A completed analysis publishes an identical descriptor digest and
 * would-submit summary regardless of the wall-clock budget, and each budget
 * cause stays distinguishable.  The fixed arena is what makes the digest
 * comparison meaningful: a fresh subject trace has no such guarantee. */
static void test_symbolic_profile_digest_is_budget_independent(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xea00;
    uint64_t baseline_digest[SNAPSHOT_SYMBOLIC_DIGEST_ROUNDS];
    uint32_t baseline_families = 0;
    uint32_t baseline_variants = 0;
    const uint64_t budgets[] = { 100, 500, 1000 };

    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_SHADOW);
    for (size_t i = 0; i < G_N_ELEMENTS(budgets); i++) {
        reset_runtime();
        symbolic_canonical_fixture(&fx, cell);
        s_symbolic_config.deadline_ms = budgets[i];
        s_symbolic_config.max_work = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_WORK;
        s_symbolic_config.max_bytes = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_BYTES;
        CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0,
              "shadow mode submits nothing at any budget");
        CHECK(s_symbolic_last_stats.analysis_complete &&
                  s_symbolic_last_stats.digest_complete,
              "shadow analysis completes and publishes a comparable set");
        CHECK(s_symbolic_last_stats.stop_reason ==
                  SNAPSHOT_SYMBOLIC_STOP_NONE,
              "no guard fires at the trial budgets");
        CHECK(s_symbolic_last_stats.would_submit_families >= 1,
              "shadow reports the families boundary mode would submit");
        if (i == 0) {
            memcpy(baseline_digest, s_symbolic_last_stats.digest,
                   sizeof(baseline_digest));
            baseline_families = s_symbolic_last_stats.would_submit_families;
            baseline_variants = s_symbolic_last_stats.would_submit_variants;
            continue;
        }
        CHECK(memcmp(baseline_digest, s_symbolic_last_stats.digest,
                     sizeof(baseline_digest)) == 0,
              "completed digest is identical across trial budgets");
        CHECK(s_symbolic_last_stats.would_submit_families == baseline_families &&
                  s_symbolic_last_stats.would_submit_variants ==
                      baseline_variants,
              "would-submit summary is identical across trial budgets");
    }

    /* Forcing a budget cause must attribute that exact cause at its stage and
     * publish no family.  The deadline guard is forced already-expired so the
     * cause cannot be raced against the wall clock. */
    reset_runtime();
    symbolic_canonical_fixture(&fx, cell);
    s_symbolic_config.deadline_ms = SNAPSHOT_SYMBOLIC_DEFAULT_DEADLINE_MS;
    s_symbolic_config.max_work = 1;
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0 &&
              s_symbolic_last_stats.stop_reason == SNAPSHOT_SYMBOLIC_STOP_WORK &&
              s_symbolic_last_stats.stop_stage ==
                  SNAPSHOT_SYMBOLIC_STAGE_SOURCES,
          "forced work exhaustion attributes the work cause to its stage");
    CHECK(!s_symbolic_last_stats.digest_complete &&
              s_symbolic_last_stats.would_submit_families == 0,
          "interrupted analysis has no comparable digest");
    {
        /* The all-zero digest is the documented incomparable marker: it must
         * never be mistaken for a real completed-set identity. */
        bool all_zero = true;
        for (uint32_t lane = 0; lane < SNAPSHOT_SYMBOLIC_DIGEST_ROUNDS; lane++) {
            if (s_symbolic_last_stats.digest[lane] != 0) all_zero = false;
        }
        CHECK(all_zero,
              "interrupted analysis leaves the digest at its incomparable "
              "all-zero marker");
    }

    /* Leave exactly enough bytes for the four top-level fixed arrays.  The
     * index reservation must then stop as a byte budget at the index stage,
     * not masquerade as a host allocation failure. */
    reset_runtime();
    symbolic_canonical_fixture(&fx, cell);
    s_symbolic_config.max_work = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_WORK;
    s_symbolic_config.max_bytes =
        (uint64_t)SNAPSHOT_SYMBOLIC_MAX_SOURCES *
            sizeof(SnapshotSymbolicSource) +
        (uint64_t)SNAPSHOT_SYMBOLIC_SOURCE_TABLE_CAPACITY *
            sizeof(SnapshotSymbolicSourceLookupEntry) +
        (uint64_t)SNAPSHOT_SYMBOLIC_MAX_SOURCES *
            SNAPSHOT_SYMBOLIC_MAX_CANDIDATES_PER_SOURCE *
            sizeof(SnapshotSymbolicCandidate) +
        (uint64_t)SNAPSHOT_SYMBOLIC_MAX_SOURCES * sizeof(uint8_t);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0 &&
              s_symbolic_last_stats.stop_reason ==
                  SNAPSHOT_SYMBOLIC_STOP_BYTES &&
              s_symbolic_last_stats.stop_stage ==
                  SNAPSHOT_SYMBOLIC_STAGE_INDEX,
          "index reservation preserves the byte-budget stop cause");
    CHECK(s_symbolic_last_stats.allocation_failures == 0 &&
              coordinator.families->len == 0,
          "index byte exhaustion is not an allocation failure or prefix");

    reset_runtime();
    symbolic_canonical_fixture(&fx, cell);
    s_symbolic_config.max_work = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_WORK;
    s_symbolic_config.max_bytes = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_BYTES;
    s_symbolic_test_deadline_expired = true;
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0 &&
              s_symbolic_last_stats.stop_reason ==
                  SNAPSHOT_SYMBOLIC_STOP_DEADLINE &&
              s_symbolic_last_stats.stop_stage ==
                  SNAPSHOT_SYMBOLIC_STAGE_SOURCES,
          "forced deadline expiry attributes the deadline cause");
    CHECK(coordinator.families->len == 0,
          "deadline exhaustion publishes no family prefix");
    s_symbolic_test_deadline_expired = false;

    /* Restoring every budget must admit the same fixture with the same
     * candidate set, so the abstentions above were the guards. */
    reset_runtime();
    symbolic_canonical_fixture(&fx, cell);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0 &&
              s_symbolic_last_stats.analysis_complete &&
              s_symbolic_last_stats.would_submit_families == baseline_families,
          "restored budgets admit the fixture with the same candidate set");

    s_symbolic_config.deadline_ms = SNAPSHOT_SYMBOLIC_DEFAULT_DEADLINE_MS;
    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* Boundary mode publishes a whole family for the same arena shadow mode only
 * summarized, and records no capacity refusal on a completed analysis.  This
 * is what makes the shadow would-submit count an actual proposal count. */
static void test_symbolic_would_submit_matches_boundary(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xea80;
    uint32_t would_submit = 0;

    reset_runtime();
    symbolic_canonical_fixture(&fx, cell);
    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_SHADOW);
    s_symbolic_config.deadline_ms = SNAPSHOT_SYMBOLIC_DEFAULT_DEADLINE_MS;
    s_symbolic_config.max_work = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_WORK;
    s_symbolic_config.max_bytes = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_BYTES;
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0,
          "shadow mode proposes nothing");
    would_submit = s_symbolic_last_stats.would_submit_families;
    CHECK(would_submit >= 1 && s_symbolic_last_stats.label_cap_refusals == 0,
          "completed shadow analysis records a would-submit count");

    reset_runtime();
    symbolic_canonical_fixture(&fx, cell);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == would_submit,
          "boundary mode submits exactly the shadow would-submit families");
    CHECK(coordinator.families->len == would_submit,
          "boundary coordinator holds one family per would-submit family");
    /* A completed submission is not a stop.  Reporting `submit/<cause>` here
     * would describe a clean run as if it had aborted at the submission
     * stage, and the exact cause field is what a trial is read for. */
    CHECK(s_symbolic_last_stats.stop_reason == SNAPSHOT_SYMBOLIC_STOP_NONE,
          "a completed boundary submission publishes no stop");
    CHECK(s_symbolic_last_stats.budget == 0 &&
              s_symbolic_last_stats.allocation_failures == 0,
          "a completed boundary submission exhausts no resource budget");

    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* `off` and `shadow` must leave the published queue identical.  Shadow runs
 * the same analysis but submits nothing, so the queue it publishes is exactly
 * the one `off` publishes -- this is the descriptor/order guarantee, checked
 * by dumping every staged plan descriptor rather than by counting plans. */
static void test_symbolic_shadow_leaves_queue_unchanged(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator off_coordinator;
    SnapshotMutationCoordinator shadow_coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xec00;
    GString *off_dump;
    GString *shadow_dump;

    /* Two independent coordinators over structurally identical fixtures. */
    reset_runtime();
    symbolic_canonical_fixture(&fx, cell);
    off_coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
    CHECK(symbolic_run_fixture(&fx, &off_coordinator, &sink) == 0,
          "off mode proposes nothing");
    off_dump = dump_staged_plans(&off_coordinator);

    reset_runtime();
    symbolic_canonical_fixture(&fx, cell);
    shadow_coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_SHADOW);
    s_symbolic_config.deadline_ms = SNAPSHOT_SYMBOLIC_DEFAULT_DEADLINE_MS;
    s_symbolic_config.max_work = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_WORK;
    s_symbolic_config.max_bytes = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_BYTES;
    CHECK(symbolic_run_fixture(&fx, &shadow_coordinator, &sink) == 0 &&
              shadow_coordinator.families->len == 0,
          "shadow mode proposes nothing");
    shadow_dump = dump_staged_plans(&shadow_coordinator);

    CHECK(strcmp(off_dump->str, shadow_dump->str) == 0,
          "off and shadow stage byte-identical plan descriptors in order");

    g_string_free(off_dump, TRUE);
    g_string_free(shadow_dump, TRUE);
    g_ptr_array_free(off_coordinator.families, TRUE);
    g_ptr_array_free(off_coordinator.staged, TRUE);
    g_ptr_array_free(shadow_coordinator.families, TRUE);
    g_ptr_array_free(shadow_coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* A submit-stage allocation failure is an advisor environment event, not a
 * sink rejection: the two are counted separately so a quota/validation
 * abstention cannot masquerade as memory pressure (or the reverse). */
/* The scheduling policy is a permutation of the same plan set: it must move
 * witness-capable plans ahead of the rest without changing membership,
 * contents, or source identity, and the default must leave the order alone. */
static bool plan_witness_capable_hint(const SnapshotMutationPlan *plan)
{
    return plan != NULL && plan->source_valid && plan->source_retained &&
           plan->read_witness_applicable && plan->read_witness.valid &&
           plan->seed_semantics == SNAPSHOT_MUTATION_SEED_OBSERVED_READ &&
           plan->source_kind == SNAPSHOT_MUTATION_SOURCE_PRIMITIVE;
}

/* Position-independent descriptor text, so the membership/contents invariant
 * is compared as a multiset rather than by index. */
static GString *dump_plan_multiset(const SnapshotMutationCoordinator *coordinator)
{
    GString *out = g_string_new(NULL);
    GString **lines = g_new0(GString *, coordinator->staged->len);

    for (guint i = 0; i < coordinator->staged->len; i++) {
        const SnapshotMutationPlan *plan =
            g_ptr_array_index(coordinator->staged, i);
        GString *line = g_string_new(NULL);

        g_string_append_printf(line,
                               "mods=%u advisor=%u ordinal=%u kind=%u "
                               "retained=%d witness=%d family=%llu",
                               plan->num_mods, plan->advisor_id,
                               plan->source_ordinal,
                               (uint32_t)plan->source_kind,
                               plan->source_retained ? 1 : 0,
                               plan->read_witness_applicable ? 1 : 0,
                               (unsigned long long)plan->family_id);
        for (uint32_t m = 0; m < plan->num_mods; m++) {
            const SnapshotMutationWrite *mod = &plan->mods[m];
            g_string_append_printf(line, " addr=%llx size=%u value=",
                                   (unsigned long long)mod->addr, mod->size);
            for (size_t b = 0; b < sizeof(mod->value); b++) {
                g_string_append_printf(line, "%02x", mod->value[b]);
            }
        }
        lines[i] = line;
    }
    for (guint i = 0; i + 1 < coordinator->staged->len; i++) {
        for (guint j = i + 1; j < coordinator->staged->len; j++) {
            if (strcmp(lines[i]->str, lines[j]->str) > 0) {
                GString *swap = lines[i];
                lines[i] = lines[j];
                lines[j] = swap;
            }
        }
    }
    for (guint i = 0; i < coordinator->staged->len; i++) {
        g_string_append(out, lines[i]->str);
        g_string_append_c(out, '\n');
        g_string_free(lines[i], TRUE);
    }
    g_free(lines);
    return out;
}

static void test_mutation_schedule_partition(void)
{
    SnapshotMutationBaseline baseline = {0};
    SnapshotMutationBaselineEntry entries[3] = {0};
    SnapshotMutationCoordinator existing = {0};
    SnapshotMutationCoordinator retained = {0};
    SnapshotMutationScheduleStats stats = {0};
    SnapshotMutationPlan *plans[3] = {NULL, NULL, NULL};
    SnapshotMutationPlan *copies[3] = {NULL, NULL, NULL};
    uint64_t existing_digest[SNAPSHOT_MUTATION_SCHEDULE_DIGEST_LANES];
    uint64_t ordered_digest[SNAPSHOT_MUTATION_SCHEDULE_DIGEST_LANES];
    uint8_t narrow[8] = {0x72};
    bool valid = false;

    baseline.run_epoch = 5;
    baseline.entry_count = G_N_ELEMENTS(entries);
    baseline.entries = entries;
    for (uint32_t i = 0; i < G_N_ELEMENTS(entries); i++) {
        entries[i].token.run_epoch = baseline.run_epoch;
        entries[i].token.source_ordinal = i;
        entries[i].lane = SNAPSHOT_MUTATION_LANE_PRIMITIVE;
        entries[i].source_kind = SNAPSHOT_MUTATION_SOURCE_PRIMITIVE;
        entries[i].eligible = true;
        entries[i].typed_eligible = true;
        entries[i].size = 1;
        entries[i].addr = TEST_GUEST_BASE + 0xa100 + i * 0x10;
        entries[i].observed_read_valid = true;
        entries[i].access_id = 5 + i;
        entries[i].pc = 0x400300 + i;
        entries[i].observed_read_bytes[0] = (uint8_t)(0x30 + i);
        entries[i].planner_bytes[0] = (uint8_t)(0x30 + i);
        entries[i].expr_index = (int64_t)(8 + i);
        entries[i].query_index = (int64_t)(2 + i);
        entries[i].root_extension = SNAPSHOT_ROOT_ZEXT;
    }

    CHECK(snapshot_mutation_schedule_parse(NULL, &valid) ==
              SNAPSHOT_MUTATION_SCHEDULE_EXISTING && valid,
          "an unset schedule value selects the historical order");
    CHECK(snapshot_mutation_schedule_parse("existing", &valid) ==
              SNAPSHOT_MUTATION_SCHEDULE_EXISTING && valid,
          "the explicit existing policy parses");
    CHECK(snapshot_mutation_schedule_parse("retained-first", &valid) ==
              SNAPSHOT_MUTATION_SCHEDULE_RETAINED_FIRST && valid,
          "the retained-first policy parses");
    /* Unknown text fails closed onto the historical order instead of silently
     * selecting an experiment. */
    CHECK(snapshot_mutation_schedule_parse("Retained-First", &valid) ==
              SNAPSHOT_MUTATION_SCHEDULE_EXISTING && !valid,
          "an unrecognized schedule value fails closed and reports invalid");

    existing.baseline = &baseline;
    existing.families = g_ptr_array_new_with_free_func(
        snapshot_mutation_proposal_family_free);
    existing.staged = g_ptr_array_new_with_free_func(
        (GDestroyNotify)snapshot_mutation_free);
    retained = existing;
    retained.families = g_ptr_array_new_with_free_func(
        snapshot_mutation_proposal_family_free);
    retained.staged = g_ptr_array_new_with_free_func(
        (GDestroyNotify)snapshot_mutation_free);

    /* Every source is retained and every plan keeps the exact-width write, so
     * the seed semantics is the only thing separating the classes: a
     * snapshot-state seed is not witness-capable however well it matches. */
    for (uint32_t i = 0; i < G_N_ELEMENTS(plans); i++) {
        bool observed_seed = i == 2;

        plans[i] = snapshot_mutation_new_descriptor(
            entries[i].addr, 1, -1, -1, SNAPSHOT_MUTATION_BYTES,
            narrow, 0, NULL);
        copies[i] = snapshot_mutation_new_descriptor(
            entries[i].addr, 1, -1, -1, SNAPSHOT_MUTATION_BYTES,
            narrow, 0, NULL);
        CHECK(plans[i] != NULL && copies[i] != NULL,
              "schedule fixture allocates both plans");
        snapshot_mutation_plan_set_source(
            plans[i], &baseline, entries[i].token,
            observed_seed ? SNAPSHOT_MUTATION_SEED_OBSERVED_READ
                          : SNAPSHOT_MUTATION_SEED_SNAPSHOT_STATE, false, 0);
        snapshot_mutation_plan_set_source(
            copies[i], &baseline, entries[i].token,
            observed_seed ? SNAPSHOT_MUTATION_SEED_OBSERVED_READ
                          : SNAPSHOT_MUTATION_SEED_SNAPSHOT_STATE, false, 0);
        CHECK(plans[i]->source_retained && plans[i]->read_witness_applicable,
              "every fixture plan is retained and witness-applicable");
        CHECK(plan_witness_capable_hint(plans[i]) == observed_seed,
              "only the observed-read seed is witness-capable");
    }

    for (uint32_t i = 0; i < G_N_ELEMENTS(plans); i++) {
        g_ptr_array_add(existing.staged, plans[i]);
        g_ptr_array_add(retained.staged, copies[i]);
    }

    snapshot_mutation_coordinator_schedule(
        &existing, SNAPSHOT_MUTATION_SCHEDULE_EXISTING, &stats);
    CHECK(stats.staged == 3 && stats.witness_capable == 1 &&
              stats.moved == 0 && !stats.allocation_failure,
          "the existing policy reports both class sizes without reordering");
    CHECK(g_ptr_array_index(existing.staged, 0) == plans[0] &&
              g_ptr_array_index(existing.staged, 2) == plans[2],
          "the existing policy publishes the advisors' own order");
    memcpy(existing_digest, stats.input_digest, sizeof(existing_digest));

    /* A required partition is allocation-atomic: failure reports the cause
     * and leaves every staged position unchanged. */
    snapshot_mutation_test_set_alloc_fail_after(0);
    snapshot_mutation_coordinator_schedule(
        &retained, SNAPSHOT_MUTATION_SCHEDULE_RETAINED_FIRST, &stats);
    snapshot_mutation_test_set_alloc_fail_after(-1);
    CHECK(stats.allocation_failure && stats.moved == 0 &&
              g_ptr_array_index(retained.staged, 0) == copies[0] &&
              g_ptr_array_index(retained.staged, 2) == copies[2],
          "schedule allocation failure preserves the complete input order");

    snapshot_mutation_coordinator_schedule(
        &retained, SNAPSHOT_MUTATION_SCHEDULE_RETAINED_FIRST, &stats);
    /* [p0,p1,p2] becomes [p2,p0,p1]: the witness plan moves to the front and
     * every position changes identity, which is what `moved` counts. */
    CHECK(stats.witness_capable == 1 && stats.moved == 3 &&
              !stats.allocation_failure,
          "retained-first moves the witness plan ahead of the other two");
    CHECK(memcmp(existing_digest, stats.input_digest,
                 sizeof(existing_digest)) == 0,
          "both policies digest the same complete pre-schedule queue");
    CHECK(g_ptr_array_index(retained.staged, 0) == copies[2],
          "the witness-capable plan runs first");
    CHECK(g_ptr_array_index(retained.staged, 1) == copies[0] &&
              g_ptr_array_index(retained.staged, 2) == copies[1],
          "the remaining plans keep their relative order");

    GString *existing_set = dump_plan_multiset(&existing);
    GString *retained_set = dump_plan_multiset(&retained);
    CHECK(strcmp(existing_set->str, retained_set->str) == 0,
          "the policy permutes the same plan set without changing contents");
    g_string_free(existing_set, TRUE);
    g_string_free(retained_set, TRUE);

    /* Re-applying the policy to an array whose witness plan is already first
     * is idempotent and needs no temporary allocation.  Leave the allocator
     * armed to fail so an avoidable allocation would make this check fail. */
    snapshot_mutation_test_set_alloc_fail_after(0);
    snapshot_mutation_coordinator_schedule(
        &retained, SNAPSHOT_MUTATION_SCHEDULE_RETAINED_FIRST, &stats);
    snapshot_mutation_test_set_alloc_fail_after(-1);
    CHECK(stats.moved == 0 && stats.witness_capable == 1 &&
              !stats.allocation_failure &&
              g_ptr_array_index(retained.staged, 0) == copies[2],
          "re-applying the policy is allocation-free and idempotent");
    memcpy(ordered_digest, stats.input_digest, sizeof(ordered_digest));
    copies[0]->mods[0].value[0] ^= 1;
    snapshot_mutation_coordinator_schedule(
        &retained, SNAPSHOT_MUTATION_SCHEDULE_EXISTING, &stats);
    CHECK(memcmp(ordered_digest, stats.input_digest,
                 sizeof(ordered_digest)) != 0,
          "the queue digest distinguishes sibling write values");

    g_ptr_array_free(existing.families, TRUE);
    g_ptr_array_free(existing.staged, TRUE);
    g_ptr_array_free(retained.families, TRUE);
    g_ptr_array_free(retained.staged, TRUE);
}

static void test_symbolic_submit_allocation_is_distinct(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xeb80;
    uint32_t analysis_allocations = 6;  /* four fixed tables, keys, labels */

    reset_runtime();
    symbolic_canonical_fixture(&fx, cell);
    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    s_symbolic_config.deadline_ms = SNAPSHOT_SYMBOLIC_DEFAULT_DEADLINE_MS;
    s_symbolic_config.max_work = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_WORK;
    s_symbolic_config.max_bytes = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_BYTES;
    /* The analysis allocations succeed; the first submit-side allocation is
     * the one that fails. */
    s_symbolic_test_alloc_fail_after = analysis_allocations;
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0 &&
              coordinator.families->len == 0,
          "submit-stage allocation failure publishes no family");
    CHECK(s_symbolic_last_stats.analysis_complete,
          "submit-stage allocation failure happens after a complete analysis");
    CHECK(s_symbolic_last_stats.allocation_failures >= 1 &&
              s_symbolic_last_stats.submission_rejections == 0,
          "submit-stage allocation failure is not a sink rejection");
    CHECK(s_symbolic_last_stats.stop_reason ==
              SNAPSHOT_SYMBOLIC_STOP_ALLOCATION &&
              s_symbolic_last_stats.stop_stage ==
                  SNAPSHOT_SYMBOLIC_STAGE_SUBMIT,
          "submit allocation failure records its exact stop cause");
    s_symbolic_test_alloc_fail_after = -1;

    reset_runtime();
    symbolic_canonical_fixture(&fx, cell);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 1 &&
              coordinator.families->len == 1,
          "restored allocation admits the same family again");

    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

/* An allocation failure is an environment event, not an unsupported
 * expression: it must be attributed separately and must publish nothing. */
static void test_symbolic_allocation_failure_cleanup(void)
{
    SymbolicFixture fx;
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    uintptr_t cell = TEST_GUEST_BASE + 0xeb00;

    /* Every advisor-owned allocation is forced to fail. */
    reset_runtime();
    symbolic_canonical_fixture(&fx, cell);
    coordinator = fixture_coordinator(&fx);
    symbolic_configure(SNAPSHOT_SYMBOLIC_BOUNDARY);
    s_symbolic_config.deadline_ms = SNAPSHOT_SYMBOLIC_DEFAULT_DEADLINE_MS;
    s_symbolic_config.max_work = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_WORK;
    s_symbolic_config.max_bytes = SNAPSHOT_SYMBOLIC_DEFAULT_MAX_BYTES;
    s_symbolic_test_alloc_fail_after = 0;
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 0 &&
              coordinator.families->len == 0,
          "allocation failure publishes no family");
    CHECK(s_symbolic_last_stats.stop_reason ==
              SNAPSHOT_SYMBOLIC_STOP_ALLOCATION &&
              s_symbolic_last_stats.allocation_failures >= 1,
          "allocation failure is attributed separately from abstention");
    CHECK(s_symbolic_last_stats.unsupported == 0,
          "allocation failure is not counted as unsupported input");
    s_symbolic_test_alloc_fail_after = -1;

    /* The same fixture with allocation restored still succeeds: cleanup left
     * no state behind that blocks a later analysis. */
    reset_runtime();
    symbolic_canonical_fixture(&fx, cell);
    CHECK(symbolic_run_fixture(&fx, &coordinator, &sink) == 1 &&
              coordinator.families->len == 1,
          "allocation failure leaves the advisor reusable");

    g_ptr_array_free(coordinator.families, TRUE);
    g_ptr_array_free(coordinator.staged, TRUE);
    symbolic_configure(SNAPSHOT_SYMBOLIC_OFF);
}

int main(void)
{
    /* The at-cap matrix records thousands of accesses; diagnostics are
     * not assertions and would obscure the focused result. */
    g_setenv("BINRADAR_TRACE_FILE", "none", TRUE);
    g_setenv("BINRADAR_TRACER_LOG_FILE", "none", TRUE);
    /* Arm the record machinery: forkserver_installed is a non-static
     * global in snapshot.c. */
    forkserver_installed = true;
    snapshot_init();
    CHECK(shared_trace_data != NULL, "shared trace data allocated");
    /* Deterministic OSPREY collection: the record writers gate capture
     * on this flag. */
    osprey_collect_enabled = 1;
    /* Back the guest addresses used by the record-level groups so
     * g2h() dereferences and pointer-target validation resolve. */
    setup_guest_memory();

    test_capture_matrix();

    test_record_width_replacement();
    test_read_token_identity();
    test_mutation_read_witness_identity();
    test_pointer_over_primitive();
    test_at_cap_sticky();
    test_generic_without_locator();
    test_parent_count_clamp();
    test_owned_generic_plan_parity();
    test_owned_generic_boundary_parity();
    test_owned_untyped_pointer_parity();
    test_owned_fresh_payloads();
    test_typed_pointer_plans_and_fallback();
    test_reference_plan_matrix();
    test_fresh_pointer_application();
    test_atomic_plan_enqueue_failures();
    test_nested_payload_failures();
    test_owned_plan_validation();
    test_mutation_coordinator_contract();
    test_manager_fifo_and_cleanup();
    test_child_multiwrite_atomicity();
    test_variant_multiwrite_child_observation();
    test_child_application_does_not_mutate_plan();
    test_forkserver_continuation_policy();
    test_invalid_patch_result();
    test_cached_feedback_writer();
    test_symbolic_feedback_matches_applied_plan();
    test_feedback_requires_representative_child();
    test_feedback_rejects_malformed_brch();
    test_symbolic_boundary_unsigned();
    test_symbolic_no_false_side();
    test_symbolic_transform_chain();
    test_symbolic_nested_extension();
    test_symbolic_reevaluates_lowered_source();
    test_symbolic_candidate_deduplication();
    test_symbolic_mask_no_preimage();
    test_symbolic_mask_preimage_found();
    test_symbolic_shadow_submits_nothing();
    test_symbolic_off_is_inert();
    test_symbolic_mirrored_constant();
    test_symbolic_unobserved_source_skipped();
    test_symbolic_work_budget_abstains();
    test_symbolic_byte_budget_abstains();
    test_symbolic_replaced_record_binds_alias();
    test_symbolic_mismatched_wrapper_not_bound();
    test_symbolic_budget_parser_is_strict();
    test_symbolic_profile_digest_is_budget_independent();
    test_symbolic_would_submit_matches_boundary();
    test_symbolic_allocation_failure_cleanup();
    test_symbolic_submit_allocation_is_distinct();
    test_mutation_schedule_partition();
    test_symbolic_shadow_leaves_queue_unchanged();

    osprey_free_runtime_regions();
    teardown_guest_memory();
    /* Free queued and current plans through the production destructor. */
    if (mod_manager != NULL) {
        snapshot_modification_manager_reset(false);
    }
    /* The analyze copies (prim_data/ptr_data) live in the original/all
     * hash tables with NULL value destroy.  The 'original' and 'all'
     * tables share the SAME copies, so free through the 'all' tables
     * only. */
    {
        GHashTable *tabs[] = {g_read_access_tainted_primitives_all,
                              g_read_access_pointers_all};
        GHashTable **aliases[] = {
            &g_read_access_tainted_primitives_original,
            &g_read_access_pointers_original};
        for (size_t t = 0; t < sizeof(tabs) / sizeof(tabs[0]); t++) {
            if (tabs[t] == NULL) continue;
            GHashTableIter it;
            gpointer key, value;
            g_hash_table_iter_init(&it, tabs[t]);
            while (g_hash_table_iter_next(&it, &key, &value)) {
                g_free(value);
            }
            g_hash_table_destroy(tabs[t]);
            if (t == 0) g_read_access_tainted_primitives_all = NULL;
            if (t == 1) g_read_access_pointers_all = NULL;
            /* The alias table references freed copies; drop it without
             * touching values. */
            if (*aliases[t] != NULL) {
                g_hash_table_destroy(*aliases[t]);
                *aliases[t] = NULL;
            }
        }
    }
    /* Drop the OSPREY context (frees the catalogs, relations, graph,
     * model, and per-CPU origin shadows) and the snapshot state. */
    if (g_osprey_ctx != NULL) {
        osprey_free(g_osprey_ctx);
        g_osprey_ctx = NULL;
    }
    if (g_snapshot.pages != NULL) {
        g_hash_table_destroy(g_snapshot.pages);
        g_snapshot.pages = NULL;
    }
    if (failures > 0) {
        fprintf(stderr, "stage7-mutation: %u/%u checks failed\n",
                failures, checks);
        return 1;
    }
    printf("stage7-mutation: %u checks passed\n", checks);
    return 0;
}