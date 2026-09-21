#include "snapshot.h"
#include "provenance.h"
#include "sem-events.h"
#include "osprey.h"
#include "osprey-internal.h"
#include "snapshot-mutation.h"
#include "snapshot-mutation-symbolic.h"
#include "e9-ranges.h"
#include "../tcg/symbolic/symbolic-struct.h"
#include "sbsv.h"
#include "qemu/rcu.h"
#include "qapi/error.h"
#include "qapi/qmp/qdict.h"
#include "qapi/qmp/qjson.h"
#include "qapi/qmp/qlist.h"
#include "qapi/qmp/qnum.h"

#include <fcntl.h>
#include <poll.h>
#include <stdio.h>
#include <stdint.h>
#include <limits.h>

#define SNAPSHOT_EXIT_DESC_LEN 256
#define SNAPSHOT_BT_DEPTH 64
#define BINRADAR_FORKSERVER_PROTOCOL_V3 0x41464c02u
// #define SNAPSHOT_DEBUG

#ifdef SNAPSHOT_DEBUG
#include <execinfo.h>
#include <signal.h>
#include <unistd.h>
#endif

#include <sys/mman.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <unistd.h>

/* Phase 4: exact syscall output sizes.  Verify the target ABI struct
 * sizes at compile time so snapshot_syscall() can invalidate exactly the
 * bytes the kernel wrote, replacing the old conservative 256-byte windows. */
_Static_assert(sizeof(struct target_stat) == 144, "x86_64 target_stat ABI size");
_Static_assert(sizeof(struct target_statfs) == 120, "x86_64 target_statfs ABI size");
_Static_assert(sizeof(struct target_statx) == 256, "x86_64 target_statx ABI size");

extern target_ulong target_brk;
bool restoring_to_snapshot;
target_ulong binradar_entrypoint = (target_ulong)-1;

extern Query *query_queue;
extern Query *next_query;
extern uint64_t symbolic_start_code;
extern uint64_t symbolic_end_code;

static uint64_t binradar_entrypoint_hit_count   = 0;
static uint64_t binradar_forkserver_target_hit_count = 1;
static int      binradar_forkserver_enable      = -1;
static int      binradar_preserve_child_queries = -1;
static int      binradar_solver_mutation_mode   = -1;
static int      binradar_forkserver_ctrl_r = -1;
static int      binradar_forkserver_stat_w = -1;
static char*    binradar_probe_file     = NULL;
static char*    binradar_query_window_file = NULL;
static uint8_t  binradar_query_window_dumped    = 0;

bool forkserver_installed = false;
unsigned char afl_fork_child;
unsigned int  afl_forksrv_pid;
/* Exact E9 exclusion intervals (loader + RESERVE + TRAMPOLINE maps of the
 * executing artifact), parsed from E9_EXCLUDE_RANGES.  Missing or empty
 * means no E9 regions. */
static e9_exclude_region *binradar_exclude_regions = NULL;
static size_t binradar_exclude_regions_len = 0;
static size_t binradar_exclude_regions_cap = 0;

typedef struct e9_relocated_call {
    target_ulong jump_addr;
    target_ulong call_site;
    target_ulong ret_addr;
} e9_relocated_call;

static e9_relocated_call *e9_relocated_calls = NULL;
static size_t e9_relocated_calls_len = 0;
static size_t e9_relocated_calls_cap = 0;

GHashTable *coverage_log_edges_cnt = NULL;
static SnapshotState g_snapshot;

#define SNAPSHOT_MEM_REG_CACHE 4
#define SNAPSHOT_STACK_LAZY_WINDOW (SNAPSHOT_PAGE_SIZE * 16)
typedef struct SnapshotMemRegionManager {
    // Determine region by address
    SnapshotMemRegion stack_region;
    // Cache
    // Don't use stack cache for now
    // int stack_cache_index;
    int heap_cache_index;
    int global_cache_index;
    // SnapshotMemRegion* stack_cache[SNAPSHOT_MEM_REG_CACHE];
    SnapshotMemRegion* heap_cache[SNAPSHOT_MEM_REG_CACHE];
    SnapshotMemRegion* global_cache[SNAPSHOT_MEM_REG_CACHE];
    // Data
    GArray *stack_data;
    GTree *heap_data;
    GArray *global_data;
} SnapshotMemRegionManager;

typedef struct DynStackFrame {
    uint64_t frame_id;
    target_ulong entry_sp;
    target_ulong min_sp;
    target_ulong call_pc;
    target_ulong ret_pc;
    target_ulong maybe_rbp;
    bool has_rbp;
    bool imprecise;
    bool synthetic;
    SnapshotMemRegion region;
} DynStackFrame;

static uint64_t next_dyn_frame_id = 1;

static SnapshotMemRegionManager mr_manager;
static GArray *pending_allocs = NULL;

/* ---- QASAN-like concrete bounds checking ---- */
int binradar_memcheck_enabled = 0;
#define HEAP_QUARANTINE_MAX_BYTES (50 * 1024 * 1024)
static GQueue *heap_quarantine = NULL;
static size_t heap_quarantine_bytes = 0;

// TODO: add trace or coverage info
typedef struct SnapshotExitInfo {
    uint32_t valid;
    uint32_t crashed;
    int32_t target_signal;
    int32_t host_signal;
    int32_t si_code;
    int32_t exit_code;
    target_ulong guest_pc;
    target_ulong guest_cs_base;
    target_ulong fault_addr;
    uintptr_t host_fault_addr;
    uint64_t guest_last_translation_block;
    /* Half-open pool cursors published by the child as raw pointer
     * differences: query_cursor counts entries after the reserved slot 0 and
     * expr_cursor counts expression-pool entries.  Scalar indexes survive the
     * parent's post-waitpid read; the child-written pointers they replace did
     * not.  -1 means "not published". */
    int64_t query_cursor;
    int64_t expr_cursor;
    // uint32_t bt_depth;
    // uintptr_t bt[SNAPSHOT_BT_DEPTH];
    char description[SNAPSHOT_EXIT_DESC_LEN];
} SnapshotExitInfo;


typedef struct ModificationManager {
    GQueue *modifications; // Queue<SnapshotMutationPlan *>
    SnapshotMutationPlan *current;
} ModificationManager;

/* Focused Stage-7 allocation-failure hook.  The production default is
 * disabled; tests set N to fail the Nth owned allocation (zero-based). */
static int64_t snapshot_mutation_alloc_fail_after = -1;

static void snapshot_mutation_test_set_alloc_fail_after(int64_t fail_after)
    G_GNUC_UNUSED;
static void snapshot_mutation_test_set_alloc_fail_after(int64_t fail_after)
{
    snapshot_mutation_alloc_fail_after = fail_after;
}

static void *snapshot_mutation_try_malloc(size_t size)
{
    if (size == 0 || snapshot_mutation_alloc_fail_after == 0) {
        return NULL;
    }
    if (snapshot_mutation_alloc_fail_after > 0) {
        snapshot_mutation_alloc_fail_after--;
    }
    return g_try_malloc(size);
}

static void *snapshot_mutation_try_malloc0(size_t size)
{
    if (size == 0 || snapshot_mutation_alloc_fail_after == 0) {
        return NULL;
    }
    if (snapshot_mutation_alloc_fail_after > 0) {
        snapshot_mutation_alloc_fail_after--;
    }
    return g_try_malloc0(size);
}

/* g_queue_pop_head() and g_queue_free_full() release links through GLib's
 * list allocator.  Links passed to g_queue_push_tail_link() must therefore
 * come from g_list_alloc(), never g_malloc(). */
static GList *snapshot_mutation_try_list_alloc(void)
{
    if (snapshot_mutation_alloc_fail_after == 0) {
        return NULL;
    }
    if (snapshot_mutation_alloc_fail_after > 0) {
        snapshot_mutation_alloc_fail_after--;
    }
    return g_list_alloc();
}

static void snapshot_mutation_free(SnapshotMutationPlan *mod)
{
    if (mod == NULL) {
        return;
    }
    if (mod->mods != NULL) {
        for (uint32_t i = 0; i < mod->num_mods; i++) {
            g_free(mod->mods[i].target.bytes);
        }
        g_free(mod->mods);
    }
    g_free(mod);
}

static void snapshot_mutation_free_batch(SnapshotMutationPlan **mods,
                                         size_t count)
{
    if (mods == NULL) {
        return;
    }
    for (uint32_t i = 0; i < count; i++) {
        snapshot_mutation_free(mods[i]);
        mods[i] = NULL;
    }
}

typedef struct PrimitiveAccess {
    int size;
    uintptr_t addr;
    uintptr_t pc;
    uint64_t access_id;
    uint64_t run_epoch;
    Expr *expr;
    /* Stage 7.1: fixed-layout runtime locator.  valid == 0 when the
     * canonical identity was not capturable; the record then stays
     * generic-eligible. */
    OspreyRuntimeChunkRef cell;
    /* Symbolic-observation metadata.  observed_read_valid is set when
     * the successful child load wrote 1..8 bytes into observed bytes;
     * root_extension and the scalar pool indexes are filled only by the
     * token finalizer after the final load root and its concretization
     * query are admitted.  Every writer resets all three. */
    uint8_t observed_read_bytes[sizeof(target_ulong)];
    uint8_t observed_read_valid;
    uint8_t root_extension;
    int64_t expr_index;
    int64_t query_index;
} PrimitiveAccess;

typedef struct PointerAccess {
    uintptr_t addr;
    uintptr_t target;
    uintptr_t pc;
    uint64_t access_id;
    uint64_t run_epoch;
    Expr *expr;
    /* Stage 7.1: locator for the pointer cell and, when the loaded
     * target is a valid non-zero address, for the target address
     * itself. */
    OspreyRuntimeChunkRef cell;
    OspreyRuntimeAddressRef target_ref;
    /* Symbolic-observation metadata; see PrimitiveAccess. */
    uint8_t observed_read_bytes[sizeof(target_ulong)];
    uint8_t observed_read_valid;
    uint8_t root_extension;
    int64_t expr_index;
    int64_t query_index;
} PointerAccess;

typedef struct SharedTraceData {
    /* Parent publishes this before each baseline child.  Every retained
     * access copies it, making stale records locally rejectable. */
    uint64_t run_epoch;
    uint32_t prim_idx;
    uint32_t ptr_idx;
    uint64_t prim_access_cnt;
    uint64_t ptr_access_cnt;
    /* Stage 7.1: sticky overflow flags.  Set when a record insertion
     * exceeds the fixed record capacity (or the record array is found
     * inconsistent); the parent then treats typed consumption as
     * unavailable and bounds its loops at the capacity.  Never reset in
     * the child: the parent reads them after waitpid. */
    uint32_t prim_overflow;
    uint32_t ptr_overflow;
    SnapshotExitInfo exit_info;
    /* Deferred provenance finding.  Lives in the shared mmap so the
     * parent can read it after waitpid even when the child was killed or
     * timed out (timeout-safe transport; see Step 5). */
    PendingProvenanceFault prov_pending_fault;
    PrimitiveAccess primitives[MAX_PRIMITIVE_ACCESS];
    PointerAccess pointers[MAX_POINTER_ACCESS];
} SharedTraceData;


typedef struct PatchedResult {
    uint32_t patch_id;
    uint32_t representative;
    GArray *br_taken; // Array<int> (0 = not taken, 1 = taken, 2 = patch crashed)
    bool is_crash;
    uint64_t fault_loc;
} PatchedResult;

typedef struct BinradarResult {
    uint32_t iter;
    PatchedResult *patch_results; // Array<PatchedResult *>, length = patch_cnt + 1
} BinradarResult;

#define BRCACHE_SNAPSHOT_MAGIC 0x48435242u
#define BRCACHE_SNAPSHOT_VERSION 1u
#define BRCACHE_FLAG_TRUNCATED 1u
#define BRCACHE_FLAG_CWE805 2u
#define BRCACHE_FLAG_INVALID 4u
#define BRCACHE_MAX_CAPTURE_BYTES (64u * 1024u * 1024u)
#define BRCACHE_MAX_MANIFEST_TOKENS (4ULL << 20)
#define BRCACHE_MAX_DESCRIPTOR 4095u
#define BRCACHE_MAX_EXPR_DEPTH 256u

typedef enum BinradarCacheFamily {
    BRCACHE_FAMILY_NONE,
    BRCACHE_FAMILY_GENERIC,
    BRCACHE_FAMILY_CWE805,
} BinradarCacheFamily;

typedef enum BinradarExprOp {
    BRCACHE_EXPR_LITERAL,
    BRCACHE_EXPR_VARIABLE,
    BRCACHE_EXPR_NOT,
    BRCACHE_EXPR_EQ,
    BRCACHE_EXPR_NE,
    BRCACHE_EXPR_GT,
    BRCACHE_EXPR_GE,
    BRCACHE_EXPR_LT,
    BRCACHE_EXPR_LE,
    BRCACHE_EXPR_ADD,
    BRCACHE_EXPR_SUB,
    BRCACHE_EXPR_MUL,
    BRCACHE_EXPR_DIV,
    BRCACHE_EXPR_REM,
    BRCACHE_EXPR_AND,
    BRCACHE_EXPR_OR,
    BRCACHE_EXPR_XOR,
    BRCACHE_EXPR_SHL,
    BRCACHE_EXPR_SHR,
} BinradarExprOp;

typedef struct BinradarExprNode {
    BinradarExprOp op;
    uint32_t left;
    uint32_t right;
    uint16_t variable;
    int64_t literal;
} BinradarExprNode;

typedef enum BinradarCacheCellKind {
    BRCACHE_CELL_REGISTER,
    BRCACHE_CELL_STACK8,
    BRCACHE_CELL_STACK16,
    BRCACHE_CELL_STACK32,
    BRCACHE_CELL_STACK64,
} BinradarCacheCellKind;

typedef struct BinradarCachePredicate {
    char *descriptor;
    GArray *expr_nodes;
    uint32_t expr_root;
    uint8_t cwe_kind;
    BinradarCacheCellKind cell_kind;
    uint32_t cell_index;
    uint8_t scale;
} BinradarCachePredicate;

typedef struct BinradarPatchSelector {
    uint32_t patch_id;
    uint32_t iteration;
    uint32_t descriptor_length;
    uint32_t descriptor_capacity;
    char descriptor[];
} BinradarPatchSelector;

typedef struct BinradarSnapshotHeader {
    uint32_t magic;
    uint32_t version;
    uint32_t patch_id;
    uint32_t branch;
    uint64_t stack_size;
    uint64_t flags;
} BinradarSnapshotHeader;

_Static_assert(sizeof(BinradarSnapshotHeader) == 32,
               "cached snapshot header layout changed");
_Static_assert(offsetof(BinradarPatchSelector, descriptor) == 16,
               "cached selector prefix changed");

typedef struct BinradarManager {
    uint32_t patch_cnt;
    int patch_fd_r;
    uint32_t *cur_patch_id; // Shared memory
    uint32_t *cur_iter; // Shared memory
    sbsv_parser *patch_result_parser;
    BinradarResult *current; // Current iteration before evidence commit
    FILE *evidence_file;
    size_t line_idx;
    char line_buf[4096];
    // Candidate patch ids (survivors from filter.br or legacy SBSV), length patch_cnt.
    // NULL means candidates are 1..patch_cnt.
    uint32_t *patch_list;
    // Max patch id that can be indexed in patch_results (allocated size = patch_max_id + 1).
    uint32_t patch_max_id;
    bool cache_enabled;
    bool cache_inference_enabled;
    BinradarCacheFamily cache_family;
    BinradarCachePredicate *cache_predicates;
    uint32_t cache_predicate_count;
    uint32_t cache_stack_size;
    int cache_fd_r;
    GByteArray *cache_bytes;
    bool cache_capture_overflow;
    BinradarPatchSelector *selector;
    size_t selector_size;
    /* Optional per-representative feedback.  Only .brcached provides the
     * complete BRCH snapshots needed by this contract. */
    char *feedback_dir;
    target_ulong poc_fault_addr;
} BinradarManager;

static SharedTraceData *shared_trace_data = NULL;
/* OSPREY in-process structural type analysis (Stage 1: shared-run fact
 * transport).  The parent allocates one fixed-layout MAP_SHARED run and
 * resets it before each fork; the child attaches and the parent merges the
 * completed sample after waitpid. */
static OspreyContext *g_osprey_ctx = NULL;
static OspreySharedRun *g_osprey_shared_run = NULL;
static GList *binradar_protected_mappings = NULL;

static OrderedMap *g_read_access_tainted_primitives = NULL;
static OrderedMap *g_read_access_pointers = NULL;

static GHashTable *g_read_access_tainted_primitives_original = NULL;
static GHashTable *g_read_access_pointers_original = NULL;

static GHashTable *g_read_access_tainted_primitives_all = NULL;
static GHashTable *g_read_access_pointers_all = NULL;

static ModificationManager *mod_manager = NULL;
/* Separate lifetime state from the owned manager pointer: after the queue is
 * exhausted the manager is destroyed, but analysis must not restart and trace
 * collection must stay disabled. */
static bool mutation_analysis_started = false;
static uint64_t next_snapshot_mutation_epoch = 0;
static int64_t snapshot_mutation_query_start = -1;
static int64_t snapshot_mutation_expr_start = -1;
static SnapshotMutationBaseline *snapshot_mutation_baseline = NULL;
static SnapshotExitInfo original_exit_info;

static BinradarManager *binradar_manager = NULL;

static BinradarResult *binradar_manager_alloc_one_iter(BinradarManager *manager) {
    if (manager == NULL) return NULL;
    BinradarResult *result = g_new0(BinradarResult, 1);
    result->iter = 0;
    result->patch_results = g_new0(PatchedResult, manager->patch_max_id + 1);
    return result;
}

static void trace_mem_flush(void);
static void snapshot_modification_manager_reset(bool analysis_started);
static void exit_with_status(int status);
static int binradar_manager_cur_patch_id(BinradarManager *manager, int new_patch_id);
static int binradar_manager_cur_iter(BinradarManager *manager, int new_iter);
static PatchedResult *get_patched_result_tmp(BinradarManager *manager,
                                             uint32_t patch_id);
bool is_e9_relocated_call(target_ulong pc, target_ulong *call_site,
                          target_ulong *ret_addr);

static int read_exact(int fd, void *buf, size_t len) {
    uint8_t *p = buf;
    size_t total = 0;

    while (total < len) {
        ssize_t n = read(fd, p + total, len - total);
        if (n == 0) {
            return -1;
        }
        if (n < 0) {
            if (errno == EINTR) {
                continue;
            }
            return -1;
        }
        total += (size_t)n;
    }

    return 0;
}

static int write_exact(int fd, const void *buf, size_t len) {
    const uint8_t *p = buf;
    size_t total = 0;

    while (total < len) {
        ssize_t n = write(fd, p + total, len - total);
        if (n < 0) {
            if (errno == EINTR) {
                continue;
            }
            return -1;
        }
        if (n == 0) {
            return -1;
        }
        total += (size_t)n;
    }

    return 0;
}

#define BR_EVIDENCE_HEADER_SIZE 16u
#define BR_EVIDENCE_FRAME_HEADER_SIZE 8u
#define BR_EVIDENCE_MAGIC "BRDATAB1"
#define BR_EVIDENCE_VERSION 1u
#define BR_EVIDENCE_KIND_FILTER 1u
#define BR_EVIDENCE_KIND_BINRADAR 3u
#define BR_EVIDENCE_RECORD_FILTER 1u
#define BR_EVIDENCE_RECORD_BINRADAR_ITERATION 4u
#define BR_EVIDENCE_MAX_FRAME (256u * 1024u * 1024u)
#define BR_EVIDENCE_GROUP_BRANCH_NULL 1u
#define BR_EVIDENCE_OUTCOME_NORMAL 1u
#define BR_EVIDENCE_OUTCOME_CRASH 2u

static uint16_t br_evidence_read_u16(const uint8_t *p)
{
    return (uint16_t)p[0] | ((uint16_t)p[1] << 8);
}

static uint32_t br_evidence_read_u32(const uint8_t *p)
{
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) |
           ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

static void br_evidence_append_u16(GByteArray *out, uint16_t value)
{
    uint8_t bytes[2] = {(uint8_t)value, (uint8_t)(value >> 8)};
    g_byte_array_append(out, bytes, sizeof(bytes));
}

static void br_evidence_append_u32(GByteArray *out, uint32_t value)
{
    uint8_t bytes[4] = {
        (uint8_t)value, (uint8_t)(value >> 8),
        (uint8_t)(value >> 16), (uint8_t)(value >> 24),
    };
    g_byte_array_append(out, bytes, sizeof(bytes));
}

static void br_evidence_append_u64(GByteArray *out, uint64_t value)
{
    uint8_t bytes[8];
    for (unsigned i = 0; i < sizeof(bytes); i++) {
        bytes[i] = (uint8_t)(value >> (i * 8u));
    }
    g_byte_array_append(out, bytes, sizeof(bytes));
}

static void br_evidence_append_uleb32(GByteArray *out, uint32_t value)
{
    do {
        uint8_t byte = (uint8_t)(value & 0x7fu);
        value >>= 7;
        if (value != 0) byte |= 0x80u;
        g_byte_array_append(out, &byte, 1);
    } while (value != 0);
}

static uint32_t br_evidence_crc32_update(uint32_t crc,
                                         const uint8_t *data, size_t len)
{
    crc = ~crc;
    for (size_t i = 0; i < len; i++) {
        crc ^= data[i];
        for (unsigned bit = 0; bit < 8; bit++) {
            uint32_t mask = (uint32_t)-(int32_t)(crc & 1u);
            crc = (crc >> 1) ^ (0xedb88320u & mask);
        }
    }
    return ~crc;
}

static uint32_t br_evidence_frame_crc(uint16_t type, uint16_t flags,
                                      const uint8_t *payload, size_t len)
{
    uint8_t prefix[4] = {
        (uint8_t)type, (uint8_t)(type >> 8),
        (uint8_t)flags, (uint8_t)(flags >> 8),
    };
    uint32_t crc = br_evidence_crc32_update(0, prefix, sizeof(prefix));
    return br_evidence_crc32_update(crc, payload, len);
}

static bool br_evidence_write_header(FILE *fp, uint16_t kind)
{
    GByteArray *header = g_byte_array_sized_new(BR_EVIDENCE_HEADER_SIZE);
    g_byte_array_append(header, (const uint8_t *)BR_EVIDENCE_MAGIC, 8);
    br_evidence_append_u16(header, BR_EVIDENCE_VERSION);
    br_evidence_append_u16(header, kind);
    br_evidence_append_u32(header, 0);
    bool ok = fwrite(header->data, 1, header->len, fp) == header->len;
    g_byte_array_free(header, TRUE);
    return ok;
}

static bool br_evidence_write_frame(FILE *fp, uint16_t type,
                                    const GByteArray *payload)
{
    if (payload->len > BR_EVIDENCE_MAX_FRAME) return false;
    GByteArray *header = g_byte_array_sized_new(
        BR_EVIDENCE_FRAME_HEADER_SIZE);
    br_evidence_append_u32(header, payload->len);
    br_evidence_append_u16(header, type);
    br_evidence_append_u16(header, 0);
    uint32_t crc = br_evidence_frame_crc(type, 0, payload->data, payload->len);
    uint8_t checksum[4] = {
        (uint8_t)crc, (uint8_t)(crc >> 8),
        (uint8_t)(crc >> 16), (uint8_t)(crc >> 24),
    };
    bool ok = fwrite(header->data, 1, header->len, fp) == header->len &&
              fwrite(payload->data, 1, payload->len, fp) == payload->len &&
              fwrite(checksum, 1, sizeof(checksum), fp) == sizeof(checksum) &&
              fflush(fp) == 0;
    g_byte_array_free(header, TRUE);
    return ok;
}

/* Parse E9_EXCLUDE_RANGES: a canonical comma-separated list of half-open
 * intervals.  Missing or empty initializes an empty collection.  A
 * malformed non-empty value is a configuration error: emit one structured
 * diagnostic and terminate before guest execution rather than continue
 * with a partial list.  The getenv() storage is never modified. */
void parse_e9_exclude_ranges(uintptr_t load_bias) {
    const char *value = getenv("E9_EXCLUDE_RANGES");
    if (value == NULL || value[0] == '\0') {
        return;
    }
    size_t len = 0;
    size_t cap = 0;
    if (e9_parse_exclude_ranges(value, load_bias, &binradar_exclude_regions,
                                &len, &cap) != 0) {
        log_msg("[snapshot] [parse-e9-exclude-range] [invalid-format] "
                "[value %s]\n", value);
        exit_with_status(1);
    }
    binradar_exclude_regions_len = len;
    binradar_exclude_regions_cap = cap;
    for (size_t i = 0; i < len; i++) {
        log_msg("[snapshot] [parse-e9-exclude-range] [start %lx] [end %lx]\n",
                (unsigned long)binradar_exclude_regions[i].start,
                (unsigned long)binradar_exclude_regions[i].end);
    }
}

static void check_env_var(const char *name) {
    char *value = getenv(name);
    if (value == NULL) {
        log_msg("[snapshot] [check-env-var] [name %s] [not-set]\n", name);
    } else {
        log_msg("[snapshot] [check-env-var] [name %s] [value %s]\n", name, value);
    }
}

void parse_e9_relocated_calls(uintptr_t load_bias) {
    // Expected format: "0x<jump>:0x<site>:0x<ret>,0x<jump>:0x<site>:0x<ret>,..."
    // One record per E9Patch CALLQ relocation: the address of the jump that
    // re-implements the call, the original call site, and the return address.
    char *value = getenv("E9_RELOCATED_CALL_JUMPS");
    if (value == NULL || value[0] == '\0') {
        return;
    }
    char *copy = g_strdup(value);
    char *saveptr = NULL;
    for (char *record = strtok_r(copy, ",", &saveptr); record != NULL;
         record = strtok_r(NULL, ",", &saveptr)) {
        char *jump_str = record;
        char *colon = strchr(record, ':');
        if (colon == NULL) {
            log_msg("[snapshot] [e9-relocated-call] [invalid-format] [record %s]\n", record);
            continue;
        }
        *colon = '\0';
        char *site_str = colon + 1;
        colon = strchr(site_str, ':');
        if (colon == NULL) {
            log_msg("[snapshot] [e9-relocated-call] [invalid-format] [record %s]\n", record);
            continue;
        }
        *colon = '\0';
        char *ret_str = colon + 1;

        if (e9_relocated_calls_len == e9_relocated_calls_cap) {
            e9_relocated_calls_cap = e9_relocated_calls_cap ? e9_relocated_calls_cap * 2 : 8;
            e9_relocated_calls = g_realloc(e9_relocated_calls,
                                           e9_relocated_calls_cap * sizeof(*e9_relocated_calls));
        }
        e9_relocated_calls[e9_relocated_calls_len].jump_addr =
            strtoull(jump_str, NULL, 16) + load_bias;
        e9_relocated_calls[e9_relocated_calls_len].call_site =
            strtoull(site_str, NULL, 16) + load_bias;
        e9_relocated_calls[e9_relocated_calls_len].ret_addr =
            strtoull(ret_str, NULL, 16) + load_bias;
        log_msg("[snapshot] [e9-relocated-call] [jump %lx] [site %lx] [ret %lx]\n",
                (unsigned long)e9_relocated_calls[e9_relocated_calls_len].jump_addr,
                (unsigned long)e9_relocated_calls[e9_relocated_calls_len].call_site,
                (unsigned long)e9_relocated_calls[e9_relocated_calls_len].ret_addr);
        e9_relocated_calls_len++;
    }
    g_free(copy);
}

bool is_e9_relocated_call(target_ulong pc, target_ulong *call_site,
                          target_ulong *ret_addr) {
    for (size_t i = 0; i < e9_relocated_calls_len; i++) {
        if (e9_relocated_calls[i].jump_addr == pc) {
            if (call_site != NULL) {
                *call_site = e9_relocated_calls[i].call_site;
            }
            if (ret_addr != NULL) {
                *ret_addr = e9_relocated_calls[i].ret_addr;
            }
            return true;
        }
    }
    return false;
}

void check_all_env_var(void) {
    // Log
    check_env_var("BINRADAR_TRACER_LOG_FILE");
    check_env_var("BINRADAR_TRACE_FILE");
    // Fuzzolic
    check_env_var("SYMBOLIC_INJECT_INPUT_MODE");
    check_env_var("SYMBOLIC_TESTCASE_NAME");
    check_env_var("PLT_INFO_FILE");
    // Forkserver releated
    check_env_var("BINRADAR_FORKSERVER_ENABLE");
    check_env_var("BINRADAR_ENTRYPOINT");
    check_env_var("BINRADAR_FORKSERVER_CTRL_R");
    check_env_var("BINRADAR_FORKSERVER_STAT_W");
    check_env_var("BINRADAR_FORKSERVER_TARGET_HIT_COUNT");
    check_env_var("BINRADAR_PRESERVE_CHILD_QUERIES");
    check_env_var("BINRADAR_PROBE_FILE");
    check_env_var("BINRADAR_QUERY_WINDOW_FILE");
    check_env_var("BINRADAR_FORKSERVER_CHILD_TIMEOUT");
    check_env_var("BINRADAR_FORKSERVER_ITERATION_TIMEOUT");
    // Memcheck related
    check_env_var("BINRADAR_MEMCHECK_ENABLE");
    // Patch related
    check_env_var("BINRADAR_PATCH_FD_R");
    check_env_var("PATCH_FD"); // Used by brpatch
    check_env_var("PATCH_ID"); // Used by brpatch, 123456
    check_env_var("BINRADAR_PATCH_CNT");
    check_env_var("BINRADAR_PATCH_FILTER_FILE");
    check_env_var("BINRADAR_EVIDENCE_FILE");
    check_env_var("BINRADAR_PATCH_CACHE_ENABLE");
    check_env_var("BINRADAR_PATCH_MANIFEST");
    check_env_var("BINRADAR_PATCH_CACHED_FD_R");
    check_env_var("PATCH_CACHED_FD");
    // e9tool patch region related
    check_env_var("E9_EXCLUDE_RANGES");
    // E9Patch relocated call jumps (jump-addr:call-site:ret-addr, comma separated)
    check_env_var("E9_RELOCATED_CALL_JUMPS");
    // Symbolic transport
    check_env_var("NO_EXTERNAL_SOLVER");
    // Shared memory
    check_env_var("EXPR_POOL_SHM_KEY");
    check_env_var("QUERY_SHM_KEY");
    check_env_var("BITMAP_SHM_KEY");
    check_env_var("BINRADAR_PATCH_SHM_KEY");
    // Symbolic boundary advisor (BinRadar only)
    check_env_var("BINRADAR_SYMBOLIC_MUTATION_MODE");
    check_env_var("BINRADAR_SYMBOLIC_MAX_WORK");
    check_env_var("BINRADAR_SYMBOLIC_MAX_BYTES");
    check_env_var("BINRADAR_SYMBOLIC_DEADLINE_MS");
    check_env_var("BINRADAR_SYMBOLIC_TEST_DETAIL");
}

void add_exclude_regions(uintptr_t load_bias) {
    parse_e9_exclude_ranges(load_bias);
}

bool is_in_e9_exclude_region(target_ulong pc) {
    return e9_is_in_exclude_region(binradar_exclude_regions,
                                   binradar_exclude_regions_len, pc);
}

void snapshot_protect_mapping(target_ulong addr, target_ulong len) {
    if (addr == (target_ulong)-1 || len == 0) {
        return;
    }
    SnapshotMapping *map = g_new(SnapshotMapping, 1);
    map->start = addr;
    map->len = len;
    binradar_protected_mappings = g_list_prepend(binradar_protected_mappings, map);
}

bool snapshot_addr_is_protected(target_ulong addr) {
    for (GList *node = binradar_protected_mappings; node != NULL; node = node->next) {
        SnapshotMapping *map = (SnapshotMapping *)node->data;
        if (map == NULL) {
            continue;
        }
        if (addr >= map->start && addr < map->start + map->len) {
            return true;
        }
    }
    return false;
}

static void exit_with_status(int status) {
    trace_mem_flush();
    snapshot_modification_manager_reset(false);
    exit(status);
}

typedef struct BinradarExprParser {
    const char *cursor;
    GArray *nodes;
    uint32_t depth;
} BinradarExprParser;

static bool binradar_parse_u64(const char **cursor, uint64_t *value)
{
    const char *p = *cursor;
    uint64_t result = 0;
    if (*p < '0' || *p > '9') return false;
    do {
        uint32_t digit = (uint32_t)(*p - '0');
        if (result > (UINT64_MAX - digit) / 10u) return false;
        result = result * 10u + digit;
        p++;
    } while (*p >= '0' && *p <= '9');
    *cursor = p;
    *value = result;
    return true;
}

static bool binradar_parse_expr(BinradarExprParser *parser,
                                uint32_t *index_out)
{
    BinradarExprNode node = {0};
    uint64_t number;
    char op;
    if (parser->depth++ >= BRCACHE_MAX_EXPR_DEPTH ||
        *parser->cursor == '\0') {
        parser->depth--;
        return false;
    }
    op = *parser->cursor++;
    if (op == 'p' || op == 'n' || op == 'v') {
        if (!binradar_parse_u64(&parser->cursor, &number)) goto invalid;
        if (op == 'v') {
            if (number > 15) goto invalid;
            node.op = BRCACHE_EXPR_VARIABLE;
            node.variable = (uint16_t)number;
        } else {
            node.op = BRCACHE_EXPR_LITERAL;
            node.literal = (int64_t)(op == 'n' ? 0u - number : number);
        }
    } else if (op == '~') {
        node.op = BRCACHE_EXPR_NOT;
        if (!binradar_parse_expr(parser, &node.left)) goto invalid;
    } else {
        switch (op) {
        case '=': node.op = BRCACHE_EXPR_EQ; break;
        case '!': node.op = BRCACHE_EXPR_NE; break;
        case '>':
            node.op = *parser->cursor == '=' ? BRCACHE_EXPR_GE
                                              : BRCACHE_EXPR_GT;
            if (*parser->cursor == '=') parser->cursor++;
            break;
        case '<':
            node.op = *parser->cursor == '=' ? BRCACHE_EXPR_LE
                                              : BRCACHE_EXPR_LT;
            if (*parser->cursor == '=') parser->cursor++;
            break;
        case '+': node.op = BRCACHE_EXPR_ADD; break;
        case '-': node.op = BRCACHE_EXPR_SUB; break;
        case '*': node.op = BRCACHE_EXPR_MUL; break;
        case '/': node.op = BRCACHE_EXPR_DIV; break;
        case '%': node.op = BRCACHE_EXPR_REM; break;
        case '&': node.op = BRCACHE_EXPR_AND; break;
        case '|': node.op = BRCACHE_EXPR_OR; break;
        case '^': node.op = BRCACHE_EXPR_XOR; break;
        case 'l': node.op = BRCACHE_EXPR_SHL; break;
        case 'r': node.op = BRCACHE_EXPR_SHR; break;
        default: goto invalid;
        }
        if (!binradar_parse_expr(parser, &node.left) ||
            !binradar_parse_expr(parser, &node.right)) goto invalid;
    }
    g_array_append_val(parser->nodes, node);
    *index_out = parser->nodes->len - 1;
    parser->depth--;
    return true;
invalid:
    parser->depth--;
    return false;
}

static bool binradar_parse_generic_predicate(BinradarCachePredicate *predicate,
                                             const char *descriptor)
{
    BinradarExprParser parser = {0};
    parser.cursor = descriptor;
    parser.nodes = g_array_new(FALSE, FALSE, sizeof(BinradarExprNode));
    if (!binradar_parse_expr(&parser, &predicate->expr_root) ||
        *parser.cursor != '\0') {
        g_array_free(parser.nodes, TRUE);
        return false;
    }
    predicate->expr_nodes = parser.nodes;
    return true;
}

static bool binradar_parse_decimal_u32(const char **cursor, uint32_t *value)
{
    uint64_t parsed;
    if (!binradar_parse_u64(cursor, &parsed) || parsed > UINT32_MAX) {
        return false;
    }
    *value = (uint32_t)parsed;
    return true;
}

static bool binradar_parse_cwe_predicate(BinradarCachePredicate *predicate,
                                         const char *descriptor)
{
    const char *p = descriptor;
    uint32_t value;
    if (p[0] != 'c' || (p[1] != '1' && p[1] != '2')) return false;
    predicate->cwe_kind = (uint8_t)(p[1] - '0');
    p += 2;
    if (*p == 'p') {
        p++;
        predicate->cell_kind = BRCACHE_CELL_REGISTER;
        if (!binradar_parse_decimal_u32(&p, &value) || value > 15) {
            return false;
        }
        predicate->cell_index = value;
    } else if (*p == 's') {
        p++;
        if (!binradar_parse_decimal_u32(&p, &value) || *p++ != 'i') {
            return false;
        }
        switch (value) {
        case 8: predicate->cell_kind = BRCACHE_CELL_STACK8; break;
        case 16: predicate->cell_kind = BRCACHE_CELL_STACK16; break;
        case 32: predicate->cell_kind = BRCACHE_CELL_STACK32; break;
        case 64: predicate->cell_kind = BRCACHE_CELL_STACK64; break;
        default: return false;
        }
        if (!binradar_parse_decimal_u32(&p, &predicate->cell_index)) {
            return false;
        }
    } else {
        return false;
    }
    if (predicate->cwe_kind == 1) {
        if (predicate->cell_kind != BRCACHE_CELL_REGISTER &&
            predicate->cell_kind != BRCACHE_CELL_STACK64) return false;
        predicate->scale = 1;
    } else {
        if (predicate->cell_kind == BRCACHE_CELL_STACK64 || *p++ != 'q' ||
            !binradar_parse_decimal_u32(&p, &value) ||
            (value != 1 && value != 2 && value != 4 && value != 8)) {
            return false;
        }
        predicate->scale = (uint8_t)value;
    }
    return *p == '\0';
}

static bool binradar_qnum_positive_u32(QObject *obj, uint32_t *value)
{
    QNum *number = qobject_to(QNum, obj);
    uint64_t parsed;
    if (number == NULL || !qnum_get_try_uint(number, &parsed) ||
        parsed == 0 || parsed > UINT32_MAX) return false;
    *value = (uint32_t)parsed;
    return true;
}

static bool binradar_manager_load_manifest(BinradarManager *manager,
                                           const char *path)
{
    gchar *content = NULL;
    gsize content_len = 0;
    GError *file_error = NULL;
    Error *json_error = NULL;
    QObject *root = NULL;
    bool ok = false;
    size_t max_descriptor = 0;

    if (!g_file_get_contents(path, &content, &content_len, &file_error)) {
        log_msg("[binradar] [cache-manifest] [error %s]\n",
                file_error != NULL ? file_error->message : "read failed");
        goto out;
    }
    root = qobject_from_json_with_token_limit(
        content, BRCACHE_MAX_MANIFEST_TOKENS, &json_error);
    if (root == NULL) {
        goto out;
    }
    QDict *dict = qobject_to(QDict, root);
    if (dict == NULL || qdict_get_try_int(dict, "version", -1) != 1) {
        log_msg("[binradar] [cache-manifest] [error invalid-version]\n");
        goto out;
    }
    const char *kind = qdict_get_try_str(dict, "kind");
    if (kind != NULL && strcmp(kind, "generic-erm") == 0) {
        manager->cache_family = BRCACHE_FAMILY_GENERIC;
    } else if (kind != NULL && strcmp(kind, "CWE805-erm") == 0) {
        manager->cache_family = BRCACHE_FAMILY_CWE805;
    } else {
        log_msg("[binradar] [cache-manifest] [error invalid-family]\n");
        goto out;
    }
    QList *rows = qobject_to(QList, qdict_get(dict, "predicates"));
    if (rows == NULL || qlist_size(rows) > UINT32_MAX - 1u) {
        log_msg("[binradar] [cache-manifest] [error invalid-predicates]\n");
        goto out;
    }
    manager->cache_predicate_count = (uint32_t)qlist_size(rows);
    manager->cache_predicates = g_new0(BinradarCachePredicate,
                                       manager->cache_predicate_count + 1u);
    const QListEntry *entry;
    uint32_t expected_id = 1;
    QLIST_FOREACH_ENTRY(rows, entry) {
        QDict *row = qobject_to(QDict, qlist_entry_obj(entry));
        uint32_t id, source_line;
        if (row == NULL ||
            !binradar_qnum_positive_u32(qdict_get(row, "id"), &id) ||
            id != expected_id ||
            !binradar_qnum_positive_u32(qdict_get(row, "source_line"),
                                        &source_line)) {
            log_msg("[binradar] [cache-manifest] [error invalid-row] "
                    "[index %u]\n", expected_id);
            goto out;
        }
        const char *descriptor = qdict_get_try_str(row, "descriptor");
        size_t descriptor_len = descriptor != NULL ? strlen(descriptor) : 0;
        if (descriptor_len == 0 || descriptor_len > BRCACHE_MAX_DESCRIPTOR) {
            log_msg("[binradar] [cache-manifest] [error descriptor-size] "
                    "[id %u]\n", id);
            goto out;
        }
        BinradarCachePredicate *predicate = &manager->cache_predicates[id];
        predicate->descriptor = g_strdup(descriptor);
        bool parsed = manager->cache_family == BRCACHE_FAMILY_GENERIC
            ? binradar_parse_generic_predicate(predicate, descriptor)
            : binradar_parse_cwe_predicate(predicate, descriptor);
        if (!parsed) {
            log_msg("[binradar] [cache-manifest] [error descriptor-grammar] "
                    "[id %u]\n", id);
            goto out;
        }
        max_descriptor = MAX(max_descriptor, descriptor_len);
        expected_id++;
    }
    for (uint32_t i = 0; i < manager->patch_cnt; i++) {
        uint32_t id = manager->patch_list != NULL ? manager->patch_list[i]
                                                  : i + 1u;
        if (id == 0 || id > manager->cache_predicate_count ||
            manager->cache_predicates[id].descriptor == NULL) {
            log_msg("[binradar] [cache-manifest] [error missing-active-id] "
                    "[id %u]\n", id);
            goto out;
        }
    }
    manager->selector_size = offsetof(BinradarPatchSelector, descriptor) +
                             max_descriptor + 1u;
    if (manager->selector_size < sizeof(BinradarPatchSelector)) {
        manager->selector_size = sizeof(BinradarPatchSelector);
    }
    ok = true;
    log_msg("[binradar] [cache-manifest] [loaded] [family %s] "
            "[predicates %u] [selector-size %zu]\n", kind,
            manager->cache_predicate_count, manager->selector_size);
out:
    if (json_error != NULL) {
        log_msg("[binradar] [cache-manifest] [json-error %s]\n",
                error_get_pretty(json_error));
        error_free(json_error);
    }
    if (file_error != NULL) g_error_free(file_error);
    qobject_unref(root);
    g_free(content);
    return ok;
}

static void binradar_manager_install_filter(BinradarManager *manager,
                                             GArray *ids,
                                             const char *path)
{
    if (ids->len == 0) {
        log_msg("[binradar] [patch-filter] [no-survivors] [file %s]\n", path);
        manager->patch_cnt = 0;
        manager->patch_max_id = 0;
        return;
    }
    manager->patch_list = g_new(uint32_t, ids->len);
    uint32_t max_id = 0;
    for (guint i = 0; i < ids->len; i++) {
        uint32_t patch = g_array_index(ids, uint32_t, i);
        manager->patch_list[i] = patch;
        max_id = MAX(max_id, patch);
    }
    manager->patch_cnt = ids->len;
    manager->patch_max_id = max_id;
    log_msg("[binradar] [patch-filter] [file %s] [cnt %u] [max-id %u]\n",
            path, manager->patch_cnt, manager->patch_max_id);
}

static bool binradar_manager_load_filter_binary(BinradarManager *manager,
                                                 const char *path,
                                                 const uint8_t *data,
                                                 size_t size)
{
    if (size < BR_EVIDENCE_HEADER_SIZE + BR_EVIDENCE_FRAME_HEADER_SIZE + 4u ||
        memcmp(data, BR_EVIDENCE_MAGIC, 8) != 0 ||
        br_evidence_read_u16(data + 8) != BR_EVIDENCE_VERSION ||
        br_evidence_read_u16(data + 10) != BR_EVIDENCE_KIND_FILTER ||
        br_evidence_read_u32(data + 12) != 0) {
        return false;
    }
    const uint8_t *frame = data + BR_EVIDENCE_HEADER_SIZE;
    uint32_t length = br_evidence_read_u32(frame);
    uint16_t type = br_evidence_read_u16(frame + 4);
    uint16_t flags = br_evidence_read_u16(frame + 6);
    size_t expected_size = BR_EVIDENCE_HEADER_SIZE +
        BR_EVIDENCE_FRAME_HEADER_SIZE + (size_t)length + 4u;
    if (length > BR_EVIDENCE_MAX_FRAME || expected_size != size ||
        type != BR_EVIDENCE_RECORD_FILTER || flags != 0 || length < 12u) {
        return false;
    }
    const uint8_t *payload = frame + BR_EVIDENCE_FRAME_HEADER_SIZE;
    uint32_t expected_crc = br_evidence_read_u32(payload + length);
    if (br_evidence_frame_crc(type, flags, payload, length) != expected_crc) {
        return false;
    }
    uint32_t total = br_evidence_read_u32(payload);
    uint32_t passed = br_evidence_read_u32(payload + 4);
    uint32_t bitmap_size = br_evidence_read_u32(payload + 8);
    if (total == UINT32_MAX ||
        (uint64_t)bitmap_size != ((uint64_t)total + 7u) / 8u ||
        length != 12u + bitmap_size) {
        return false;
    }
    const uint8_t *bitmap = payload + 12;
    if (total % 8u != 0 && bitmap_size > 0 &&
        (bitmap[bitmap_size - 1u] >> (total % 8u)) != 0) {
        return false;
    }
    GArray *ids = g_array_sized_new(FALSE, FALSE, sizeof(uint32_t), passed);
    for (uint32_t patch = 1; patch <= total; patch++) {
        if (bitmap[(patch - 1u) / 8u] & (1u << ((patch - 1u) % 8u))) {
            g_array_append_val(ids, patch);
        }
    }
    if (ids->len != passed || passed != manager->patch_cnt) {
        g_array_free(ids, TRUE);
        return false;
    }
    binradar_manager_install_filter(manager, ids, path);
    g_array_free(ids, TRUE);
    return true;
}

static void binradar_manager_load_filter(BinradarManager *manager,
                                         const char *path)
{
    gchar *contents = NULL;
    gsize size = 0;
    if (!g_file_get_contents(path, &contents, &size, NULL)) {
        log_msg("[binradar] [patch-filter] [error read] [file %s]\n", path);
        exit_with_status(1);
    }
    if (size >= 8 && memcmp(contents, BR_EVIDENCE_MAGIC, 8) == 0) {
        bool ok = binradar_manager_load_filter_binary(
            manager, path, (const uint8_t *)contents, size);
        g_free(contents);
        if (!ok) {
            log_msg("[binradar] [patch-filter] [error binary] [file %s]\n",
                    path);
            exit_with_status(1);
        }
        return;
    }
    g_free(contents);

    FILE *fp = fopen(path, "r");
    if (fp == NULL) {
        log_msg("[binradar] [patch-filter] [error open] [file %s]\n", path);
        exit_with_status(1);
    }
    sbsv_parser *parser = sbsv_parser_new(SBSV_PARSER_DEFAULT);
    sbsv_parser_add_schema(parser, "[patch] [id: int] [pass: bool]");
    sbsv_status status = sbsv_parser_load_file(parser, fp);
    fclose(fp);
    if (status != SBSV_OK) {
        log_msg("[binradar] [patch-filter] [error parse] [file %s] "
                "[status %s]\n", path, sbsv_status_str(status));
        sbsv_parser_free(parser);
        exit_with_status(1);
    }
    const sbsv_row **rows = NULL;
    size_t count = 0;
    if (sbsv_parser_get_rows(parser, "patch", &rows, &count) != SBSV_OK) {
        sbsv_parser_free(parser);
        exit_with_status(1);
    }
    GArray *ids = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    for (size_t i = 0; i < count; i++) {
        long long id = sbsv_row_get_int(rows[i], "id", NULL);
        int pass = sbsv_row_get_bool(rows[i], "pass", NULL);
        if (pass && id > 0 && (uint64_t)id <= UINT32_MAX) {
            uint32_t patch = (uint32_t)id;
            g_array_append_val(ids, patch);
        }
    }
    sbsv_free_row_ref_array(rows);
    sbsv_parser_free(parser);
    if (ids->len != manager->patch_cnt) {
        g_array_free(ids, TRUE);
        log_msg("[binradar] [patch-filter] [error count] [file %s]\n", path);
        exit_with_status(1);
    }
    binradar_manager_install_filter(manager, ids, path);
    g_array_free(ids, TRUE);
}

void snapshot_init_binradar_patch_shm(uintptr_t key) {
    const char *var;
    size_t shm_size = sizeof(uint32_t) * 2u;
    binradar_manager = g_new0(BinradarManager, 1);
    binradar_manager->patch_cnt = 1;
    binradar_manager->patch_fd_r = -1;
    binradar_manager->cache_fd_r = -1;

    var = getenv("BINRADAR_PATCH_CNT");
    if (var == NULL || atoi(var) < 0) {
        log_msg("BINRADAR_PATCH_CNT not set or invalid\n");
        exit_with_status(1);
    }
    binradar_manager->patch_cnt = (uint32_t)atoi(var);
    binradar_manager->patch_max_id = binradar_manager->patch_cnt;
    var = getenv("BINRADAR_PATCH_FILTER_FILE");
    if (var != NULL && var[0] != '\0') {
        binradar_manager_load_filter(binradar_manager, var);
    }

    var = getenv("BINRADAR_EVIDENCE_FILE");
    if (var == NULL || var[0] == '\0') {
        log_msg("[binradar] [evidence] [error missing-path]\n");
        exit_with_status(1);
    }
    binradar_manager->evidence_file = fopen(var, "wb");
    if (binradar_manager->evidence_file == NULL ||
        !br_evidence_write_header(binradar_manager->evidence_file,
                                  BR_EVIDENCE_KIND_BINRADAR) ||
        fflush(binradar_manager->evidence_file) != 0) {
        log_msg("[binradar] [evidence] [error open] [file %s]\n", var);
        exit_with_status(1);
    }
    log_msg("[binradar] [evidence] [file %s] [version 1]\n", var);

    var = getenv("BINRADAR_PATCH_CACHE_ENABLE");
    binradar_manager->cache_enabled = var != NULL && strcmp(var, "1") == 0;
    binradar_manager->cache_inference_enabled =
        binradar_manager->cache_enabled;
    if (binradar_manager->cache_enabled) {
        const char *manifest = getenv("BINRADAR_PATCH_MANIFEST");
        const char *cache_fd = getenv("BINRADAR_PATCH_CACHED_FD_R");
        if (manifest == NULL || manifest[0] == '\0' || cache_fd == NULL ||
            atoi(cache_fd) <= 2 ||
            !binradar_manager_load_manifest(binradar_manager, manifest)) {
            log_msg("[binradar] [cache-manifest] [fatal configuration]\n");
            exit_with_status(1);
        }
        binradar_manager->cache_fd_r = atoi(cache_fd);
        if (binradar_manager->cache_family == BRCACHE_FAMILY_CWE805) {
            uint64_t required = 0;
            for (uint32_t i = 0; i < binradar_manager->patch_cnt; i++) {
                uint32_t id = binradar_manager->patch_list != NULL
                    ? binradar_manager->patch_list[i] : i + 1u;
                BinradarCachePredicate *predicate =
                    &binradar_manager->cache_predicates[id];
                uint64_t width;
                switch (predicate->cell_kind) {
                case BRCACHE_CELL_REGISTER: width = 0; break;
                case BRCACHE_CELL_STACK8: width = 1; break;
                case BRCACHE_CELL_STACK16: width = 2; break;
                case BRCACHE_CELL_STACK32: width = 4; break;
                case BRCACHE_CELL_STACK64: width = 8; break;
                default: width = UINT64_MAX; break;
                }
                uint64_t bytes = width == UINT64_MAX ? UINT64_MAX :
                    (width == 0 ? 0 :
                     ((uint64_t)predicate->cell_index + 1u) * width);
                required = MAX(required, bytes);
            }
            const char *stack_size = getenv("BRCACHE_STACK_SIZE");
            char *end = NULL;
            errno = 0;
            uint64_t parsed = stack_size != NULL
                ? strtoull(stack_size, &end, 0) : 0;
            if (stack_size == NULL || stack_size[0] == '\0' || errno != 0 ||
                end == stack_size || *end != '\0' || parsed < required ||
                parsed > (1u << 20)) {
                log_msg("[binradar] [cache-manifest] "
                        "[error invalid-stack-size] [required %" PRIu64 "]\n",
                        required);
                exit_with_status(1);
            }
            binradar_manager->cache_stack_size = (uint32_t)parsed;
        }
        shm_size = binradar_manager->selector_size;
        binradar_manager->cache_bytes = g_byte_array_new();
    }

    const char *feedback_dir = getenv("BINRADAR_FEEDBACK_DIR");
    if (feedback_dir != NULL && feedback_dir[0] != '\0') {
        if (!binradar_manager->cache_enabled) {
            log_msg("[binradar] [feedback] [disabled] "
                    "[reason brcached-required]\n");
        } else {
            const char *fault_text = getenv("BINRADAR_POC_FAULT_ADDR");
            char *end = NULL;
            errno = 0;
            unsigned long long fault = fault_text != NULL
                ? strtoull(fault_text, &end, 0) : 0;
            if (fault_text == NULL || fault_text[0] == '\0' || errno != 0 ||
                end == fault_text || *end != '\0' ||
                (target_ulong)fault != fault ||
                !g_file_test(feedback_dir, G_FILE_TEST_IS_DIR)) {
                log_msg("[binradar] [feedback] [error configuration]\n");
                exit_with_status(1);
            }
            binradar_manager->feedback_dir = g_strdup(feedback_dir);
            binradar_manager->poc_fault_addr = (target_ulong)fault;
            log_msg("[binradar] [feedback] [enabled] [dir %s] "
                    "[poc-fault-addr %lx]\n", feedback_dir,
                    binradar_manager->poc_fault_addr);
        }
    }

    int shmid = shmget((key_t)key, shm_size, 0666 | IPC_CREAT);
    if (shmid == -1) {
        perror("shmget failed");
        exit_with_status(1);
    }
    uint32_t *shm = shmat(shmid, NULL, 0);
    if (shm == (void *)-1) {
        perror("shmat failed");
        exit_with_status(1);
    }
    memset(shm, 0, shm_size);
    binradar_manager->cur_patch_id = shm;
    binradar_manager->cur_iter = shm + 1;
    if (binradar_manager->cache_enabled) {
        binradar_manager->selector = (BinradarPatchSelector *)shm;
        /* Iteration 0 is unpublished.  An E9 call may run before the guest
         * reaches BINRADAR_ENTRYPOINT and starts the forkserver; the cached
         * runtime must preserve original control flow until iteration 1. */
        binradar_manager->selector->patch_id = 0;
        binradar_manager->selector->iteration = 0;
        binradar_manager->selector->descriptor_length = 0;
        binradar_manager->selector->descriptor_capacity =
            (uint32_t)(shm_size - offsetof(BinradarPatchSelector,
                                           descriptor));
        binradar_manager->selector->descriptor[0] = '\0';
    }

    var = getenv("BINRADAR_PATCH_FD_R");
    if (var == NULL || atoi(var) <= 2) {
        log_msg("BINRADAR_PATCH_FD_R not set\n");
        exit_with_status(1);
    }
    binradar_manager->patch_fd_r = atoi(var);
    binradar_manager->current = binradar_manager_alloc_one_iter(
        binradar_manager);
    binradar_manager->patch_result_parser = sbsv_parser_new(
        SBSV_PARSER_DEFAULT);
    sbsv_parser_add_schema(binradar_manager->patch_result_parser,
        "[patch] [id: int] [br: int] [v: int]");
}

static void snapshot_load_binradar_env(void) {
    if (binradar_forkserver_enable != -1) return;

    binradar_forkserver_enable      = 1;
    binradar_preserve_child_queries = 0;
    binradar_solver_mutation_mode = 0;

    const char* var = getenv("BINRADAR_FORKSERVER_ENABLE");
    if (var) {
        binradar_forkserver_enable = atoi(var) != 0;
    }

    var = getenv("BINRADAR_FORKSERVER_CTRL_R");
    if (var) {
        binradar_forkserver_ctrl_r = atoi(var);
    }
    var = getenv("BINRADAR_FORKSERVER_STAT_W");
    if (var) {
        binradar_forkserver_stat_w = atoi(var);
    }

    var = getenv("BINRADAR_FORKSERVER_TARGET_HIT_COUNT");
    if (var) {
        uint64_t target = strtoull(var, NULL, 10);
        if (target == ULLONG_MAX) {
            target = 0;
        }
        binradar_forkserver_target_hit_count = target;
    }

    var = getenv("BINRADAR_PRESERVE_CHILD_QUERIES");
    if (var) {
        binradar_preserve_child_queries = atoi(var) != 0;
    }

    binradar_probe_file = getenv("BINRADAR_PROBE_FILE");
    if (binradar_probe_file && binradar_probe_file[0] == '\0') {
        binradar_probe_file = NULL;
    }

    binradar_query_window_file = getenv("BINRADAR_QUERY_WINDOW_FILE");
    if (binradar_query_window_file && binradar_query_window_file[0] == '\0') {
        binradar_query_window_file = NULL;
    }

    var = getenv("BINRADAR_MEMCHECK_ENABLE");
    if (var) {
        binradar_memcheck_enabled = atoi(var) != 0;
    }
    log_msg("[snapshot-load-binradar] [forkserver %d] [hit-count %lu] [probe-file %s] [query-window-file %s] [memcheck %d]\n",
              binradar_forkserver_enable, binradar_forkserver_target_hit_count,
              binradar_probe_file ? binradar_probe_file : "null",
              binradar_query_window_file ? binradar_query_window_file : "null",
              binradar_memcheck_enabled);
}

static void snapshot_dump_query_window(Query* q, Expr *e) {
    snapshot_load_binradar_env();
    if (binradar_query_window_dumped || binradar_query_window_file == NULL) {
        return;
    }
    if (q == NULL || e == NULL) {
        return;
    }

    int64_t start_index = GET_QUERY_IDX(next_query);
    int64_t end_index = GET_QUERY_IDX(q);
    // Preserve query window for first run
    next_query = q;
    next_free_expr = e;

    FILE *fp = fopen(binradar_query_window_file, "a");
    if (fp == NULL) {
        fprintf(stderr, "Failed to open binradar query window file: %s\n", binradar_query_window_file);
        return;
    }

    fprintf(fp, "[query-window] [start %ld] [end %ld]\n", start_index, end_index - 1);
    fclose(fp);
    binradar_query_window_dumped = 1;
}

uint8_t snapshot_on_entrypoint_hit(target_ulong pc) {
    snapshot_load_binradar_env();
    binradar_entrypoint_hit_count += 1;

    log_msg("[snapshot] [entrypoint-hit] [pc %lx] [count %lu] [target %lu]\n",
              pc, binradar_entrypoint_hit_count,
              binradar_forkserver_target_hit_count);

    if (!binradar_forkserver_enable) return 0;
    if (binradar_forkserver_target_hit_count == 0) return 0;
    return binradar_entrypoint_hit_count == binradar_forkserver_target_hit_count;
}

static int use_trace = -1;
static int trace_fd = -1;
static int use_log = -1;
static int log_fd = -1;

static void trace_mem_init(void) {
    if (use_trace != -1) return;
    char* trace_file = getenv("BINRADAR_TRACE_FILE");
    if (trace_file == NULL) {
        use_trace = 1;
        trace_fd = STDERR_FILENO;
    } else if (strcmp(trace_file, "none") == 0) {
        use_trace = 0;
    } else {
        use_trace = 1;
        trace_fd = open(trace_file, O_WRONLY | O_CREAT | O_APPEND, 0644);
        if (trace_fd < 0) {
            fprintf( stderr, "ERROR: cannot open trace file %s\n",
                    trace_file);
            exit_with_status(1);
        }
    }
}

static void log_msg_init(void) {
    if (use_log != -1) return;
    char* log_file = getenv("BINRADAR_TRACER_LOG_FILE");
    if (log_file == NULL) {
        use_log = 1;
        log_fd = STDERR_FILENO;
    } else if (strcmp(log_file, "none") == 0) {
        use_log = 0;
    } else {
        use_log = 1;
        log_fd = open(log_file, O_WRONLY | O_CREAT | O_APPEND, 0644);
        if (log_fd < 0) {
            fprintf( stderr, "ERROR: cannot open log file %s\n",
                    log_file);
            exit_with_status(1);
        }
    }
}

void trace_mem(const char* fmt, ...) {
    trace_mem_init();
    if (!use_trace)
        return;
    if (mutation_analysis_started) {
        /* Analysis stays complete after the owned manager is destroyed. */
        return;
    }
    va_list ap;
    char buf[4096];
    va_start(ap, fmt);
    int n = vsnprintf(buf, sizeof(buf), fmt, ap);
    va_end(ap);
    ssize_t wr;
    if (n < 0) {
        return;
    }
    if (n >= sizeof(buf)) {
        // This should not happen
        wr = write(trace_fd, buf, sizeof(buf) - 1);
        wr = write(trace_fd, "\n[ERROR] [TRUNCATED]\n", 21);
    } else {
        wr = write(trace_fd, buf, n);
    }
    (void)wr;
}

void log_msg(const char* fmt, ...) {
    log_msg_init();
    if (!use_log)
        return;
    va_list ap;
    char buf[4096];
    va_start(ap, fmt);
    int n = vsnprintf(buf, sizeof(buf), fmt, ap);
    va_end(ap);
    ssize_t wr;
    if (n < 0) {
        return;
    }
    if (n >= sizeof(buf)) {
        // This should not happen
        wr = write(log_fd, buf, sizeof(buf) - 1);
        wr = write(log_fd, "\n[ERROR] [TRUNCATED]\n", 21);
    } else {
        wr = write(log_fd, buf, n);
    }
    (void)wr;
}

void trace_mem_flush(void) {
    if (!use_trace) return;
    if (trace_fd > 2)
        fsync(trace_fd);
}

static void log_msg_flush(void) {
    if (!use_log) return;
    if (log_fd > 2)
        fsync(log_fd);
}

const char *snapshot_mem_region_str(SnapshotMemRegion *mr) {
    if (mr == NULL) return "NULL";
    if (mr->is_stack) {
        return "stack";
    } else if (mr->is_heap) {
        return "heap";
    } else {
        return "global";
    }
}

OrderedMap *ordered_map_init(int max_size) {
    OrderedMap *map = g_new(OrderedMap, 1);
    map->max_size = max_size;
    map->table = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, g_free);
    map->queue = g_queue_new();
    return map;
}

OrderedMapEntry *ordered_map_insert(OrderedMap *map, uintptr_t key, void *data) {
    OrderedMapEntry *existing = g_hash_table_lookup(map->table, GSIZE_TO_POINTER(key));
    int old_index = -1;
    if (existing != NULL) {
        old_index = existing->shared_index;
        g_queue_delete_link(map->queue, existing->node);
        g_hash_table_remove(map->table, GSIZE_TO_POINTER(key));
    }

    if (map->max_size > 0 && g_queue_get_length(map->queue) >= map->max_size) {
        OrderedMapEntry *oldest_entry = (OrderedMapEntry *)g_queue_pop_head(map->queue);
        if (oldest_entry != NULL) {
            old_index = oldest_entry->shared_index;
            uintptr_t old_key = oldest_entry->key;
            g_hash_table_remove(map->table, GSIZE_TO_POINTER(old_key));
        }
    }

    OrderedMapEntry *entry = g_new(OrderedMapEntry, 1);
    memset(entry, 0, sizeof(OrderedMapEntry));
    entry->key = key;
    entry->data = data;
    entry->shared_index = old_index;

    g_queue_push_tail(map->queue, entry);
    entry->node = map->queue->tail;
    g_hash_table_insert(map->table, GSIZE_TO_POINTER(key), entry);
    return entry;
}

OrderedMapEntry* ordered_map_lookup(OrderedMap *map, uintptr_t key) {
    OrderedMapEntry *entry = (OrderedMapEntry *)g_hash_table_lookup(map->table, GSIZE_TO_POINTER(key));
    return entry;
}

guint coverage_edge_hash(gconstpointer key) {
    const CoverageEdge* edge = (const CoverageEdge*)key;
    guint h1 = g_int64_hash(&edge->from);
    guint h2 = g_int64_hash(&edge->to);
    return h1 ^ (h2 << 1);
}

gboolean coverage_edge_equal(gconstpointer a, gconstpointer b) {
    const CoverageEdge* edge_a = (const CoverageEdge*)a;
    const CoverageEdge* edge_b = (const CoverageEdge*)b;
    return (edge_a->from == edge_b->from) && (edge_a->to == edge_b->to);
}

CoverageEdge* coverage_edge_copy(const CoverageEdge* edge) {
    CoverageEdge *copy = g_new(CoverageEdge, 1);
    copy->from = edge->from;
    copy->to   = edge->to;
    return copy;
}


static SnapshotExitInfo *snapshot_exit_info_ptr(void) {
    if (shared_trace_data == NULL) return NULL;
    return &shared_trace_data->exit_info;
}

static void snapshot_exit_info_capture(SnapshotExitInfo *info, CPUArchState *env) {
    if (!info || !env) return;
    target_ulong pc = 0;
    target_ulong cs_base = 0;
    uint32_t flags = 0;
    cpu_get_tb_cpu_state(env, &pc, &cs_base, &flags);
    info->guest_pc = pc;
    info->guest_cs_base = cs_base;
    info->guest_last_translation_block = last_translation_block;
    info->query_cursor = (next_query != NULL && query_queue != NULL)
        ? (int64_t)(next_query - query_queue) : -1;
    info->expr_cursor = (next_free_expr != NULL && pool != NULL)
        ? (int64_t)(next_free_expr - pool) : -1;
}

static int64_t snapshot_query_cursor_index(const SnapshotExitInfo *info) {
    return info != NULL ? info->query_cursor : -1;
}

static int64_t snapshot_expr_cursor_index(const SnapshotExitInfo *info) {
    return info != NULL ? info->expr_cursor : -1;
}

/* Validate a child-published pool cursor once in the parent.  Cursors are raw
 * pointer differences into the shared pools, so they must be non-negative and
 * within the fixed capacity before any pointer is reconstructed from them. */
static bool snapshot_query_cursor_valid(int64_t cursor) {
    return cursor >= 0 && (uint64_t)cursor <= (uint64_t)EXPR_QUERY_CAPACITY;
}

static bool snapshot_expr_cursor_valid(int64_t cursor) {
    return cursor >= 0 && (uint64_t)cursor <= (uint64_t)EXPR_POOL_CAPACITY;
}

static void snapshot_log_cursor_indices(const SnapshotExitInfo *info) {
    log_msg("[snapshot] [cursors] [query_cursor %ld] [expr_cursor %ld]\n",
            snapshot_query_cursor_index(info),
            snapshot_expr_cursor_index(info));
}

static void snapshot_exit_info_set_reason(SnapshotExitInfo *info, const char *reason) {
    if (!info) return;
    if (!reason) {
        info->description[0] = '\0';
        return;
    }
    g_strlcpy(info->description, reason, SNAPSHOT_EXIT_DESC_LEN);
}

static bool snapshot_exit_info_should_update(const SnapshotExitInfo *info, bool crashed) {
    if (info == NULL) return false;
    if (!info->valid) return true;
    return crashed;  // Prevent update for exit() after error handling
}

static void dump_coverage_edge_log(gboolean update) {
    return;
    if (coverage_log_edges_cnt == NULL) return;
    GHashTableIter iter;
    gpointer key, value;
    g_hash_table_iter_init(&iter, coverage_log_edges_cnt);
    while (g_hash_table_iter_next(&iter, &key, &value)) {
        CoverageEdge *edge = (CoverageEdge *)key;
        uint64_t *cnt = (uint64_t *)value;
        if (update) {
            trace_mem("[cov] [update] [from %lx] [to %lx] [cnt %lu]\n", edge->from, edge->to, *cnt);
        } else {
            trace_mem("[cov] [base] [from %lx] [to %lx] [cnt %lu]\n", edge->from, edge->to, *cnt);
        }
    }
    if (!update) {
        g_hash_table_destroy(coverage_log_edges_cnt);
        coverage_log_edges_cnt = NULL;
    }
}

void snapshot_record_guest_normal_exit(CPUArchState *cpu_env, int exit_code, const char *reason) {
    /* Deferred provenance finding: finalize as a synthetic crash unless a
     * real crash already won the exit-info slot (deterministic precedence,
     * FIX_TRACER.md §8 / test 21). */
	if (provenance_finalize_fault(cpu_env)) {
		ProvPublishedFinding fault;
		if (!provenance_snapshot_pending_finding(&fault)) {
			/* Finding disappeared between finalize and snapshot. */
			return;
		}
		const char *pf_reason = provenance_fault_reason();
		/* Emit the structured finding exactly once, even when a real
		 * crash already won the exit-info slot: §8 requires preserving
		 * BOTH records (the pending provenance event and the real
		 * signal), with the real crash selecting the verdict. */
		provenance_report_pending_finding();

		SnapshotExitInfo *info = snapshot_exit_info_ptr();
		if (info->valid && info->crashed) {
			/* Real crash already recorded — the earlier record wins the
			 * verdict; the finding was preserved above. */
			return;
		}
		snapshot_record_guest_crash(cpu_env, TARGET_SIGSEGV, 0,
		                            SEGV_ACCERR, fault.payload.access_pc, 0,
		                            pf_reason);
		/* Crash record stores fault_addr = guest_pc (code address).
		 * Re-expose the provenance access PC for diagnostics. */
		info = snapshot_exit_info_ptr();
		info->fault_addr = fault.payload.access_pc;
		return;
	}

    SnapshotExitInfo *info = snapshot_exit_info_ptr();
    if (!snapshot_exit_info_should_update(info, false)) return;
    info->valid = 1;
    info->crashed = 0;
    info->exit_code = exit_code;
    snapshot_exit_info_capture(info, cpu_env);
    snapshot_exit_info_set_reason(info, reason ? reason : "normal_exit");
	log_msg("[snapshot] [exit] [normal] [entrypoint-hit %lu]\n",
	        binradar_entrypoint_hit_count);
	snapshot_log_cursor_indices(info);
    if (binradar_manager) {
        int patch_id = binradar_manager_cur_patch_id(binradar_manager, -1);
        int iter = binradar_manager_cur_iter(binradar_manager, -1);
        log_msg("[binradar] [normal] [iter %d] [patch %d] [guest_pc %lx] [guest_cs_base %lx] [reason %s]\n",
                  iter, patch_id, info->guest_pc, info->guest_cs_base, reason ? reason : "normal_exit");
    }
    
    dump_coverage_edge_log(true);
}

void snapshot_record_guest_crash(CPUArchState *cpu_env, int target_signal, int host_signal, int si_code, target_ulong fault_addr, uintptr_t host_fault_addr, const char *reason) {
    snapshot_load_binradar_env();
    SnapshotExitInfo *info = snapshot_exit_info_ptr();
    if (!snapshot_exit_info_should_update(info, true)) return;
    info->valid = 1;
    info->crashed = 1;
    info->target_signal = target_signal;
    info->host_signal = host_signal;
    info->si_code = si_code;
    info->exit_code = (host_signal > 0) ? (128 + host_signal) : -target_signal;
    info->host_fault_addr = host_fault_addr;
    snapshot_exit_info_capture(info, cpu_env);
    /* The binradar comparison matches this against the probe's [fault-addr],
     * which is a code address (the faulting instruction).  Store guest_pc
     * here rather than the siginfo data address so both sides agree. */
    info->fault_addr = info->guest_pc;
    char buffer[SNAPSHOT_EXIT_DESC_LEN];
    const char *base = reason ? reason : "unhandled signal";
    const char *host_name = (host_signal > 0) ? strsignal(host_signal) : NULL;
    if (host_name) {
        g_snprintf(buffer, sizeof(buffer), "%s (host=%s[%d], target=%d)", base, host_name, host_signal, target_signal);
    } else {
        g_snprintf(buffer, sizeof(buffer), "%s (host=%d, target=%d)", base, host_signal, target_signal);
    }
    snapshot_exit_info_set_reason(info, buffer);
	log_msg("[snapshot] [exit] [crash] [entrypoint-hit %lu]\n",
	        binradar_entrypoint_hit_count);
	snapshot_log_cursor_indices(info);
	log_msg("[snapshot] [crash] [hit-count %lu] [reason %s] [guest_pc %lx] [guest_cs_base %lx] [fault_addr %lx] [host_fault_addr %lx]\n",
	            binradar_entrypoint_hit_count, buffer, info->guest_pc, info->guest_cs_base, info->fault_addr, info->host_fault_addr);
    if (binradar_manager) {
        int patch_id = binradar_manager_cur_patch_id(binradar_manager, -1);
        int iter = binradar_manager_cur_iter(binradar_manager, -1);
        log_msg("[binradar] [crash] [iter %d] [patch %d] [guest_pc %lx] [guest_cs_base %lx] [fault_addr %lx] [host_fault_addr %lx] [reason %s]\n",
                  iter, patch_id, info->guest_pc, info->guest_cs_base, info->fault_addr, info->host_fault_addr, buffer);
    }
    
    if (binradar_probe_file) {
        FILE *binradar_probe_file_fp = fopen(binradar_probe_file, "a");
        if (binradar_probe_file_fp == NULL) {
            fprintf(stderr, "Failed to open binradar probe file: %s\n", binradar_probe_file);
            return;
        }
        fprintf(binradar_probe_file_fp, "[snapshot] [crash] [hit-count %lu] [reason %s] [guest_pc %lx] [guest_cs_base %lx] [fault_addr %lx] [host_fault_addr %lx]\n",
                binradar_entrypoint_hit_count, buffer, info->guest_pc, info->guest_cs_base, info->fault_addr, info->host_fault_addr);
        fclose(binradar_probe_file_fp);
    }
    dump_coverage_edge_log(true);
}

static bool reserve_read_access_index(uint32_t *counter, uint32_t capacity,
                                      uint32_t *index_out) {
    uint32_t current = __atomic_load_n(counter, __ATOMIC_RELAXED);
    for (;;) {
        if (current >= capacity) {
            return false;
        }
        uint32_t next = current + 1;
        if (__atomic_compare_exchange_n(counter, &current, next, false,
                                        __ATOMIC_RELAXED,
                                        __ATOMIC_RELAXED)) {
            *index_out = current;
            return true;
        }
    }
}

static void remove_read_access_primitive(uintptr_t addr) {
    if (g_read_access_tainted_primitives == NULL) return;
    OrderedMapEntry *entry = ordered_map_lookup(g_read_access_tainted_primitives, addr);
    if (entry == NULL) return;
    // Remove from queue
    int idx_to_remove = entry->shared_index;
    g_queue_delete_link(g_read_access_tainted_primitives->queue, entry->node);
    uint32_t count = __atomic_load_n(&shared_trace_data->prim_idx,
                                     __ATOMIC_RELAXED);
    if (idx_to_remove < 0 || count == 0 ||
        count > MAX_PRIMITIVE_ACCESS || (uint32_t)idx_to_remove >= count) {
        /* Never underflow the published count or index the fixed array
         * from inconsistent ordered-map state. */
        shared_trace_data->prim_overflow = 1;
        trace_mem("[rpi] ERROR! remove primitive failed! idx %d count %u\n",
                  idx_to_remove, count);
        g_hash_table_remove(g_read_access_tainted_primitives->table,
                            GSIZE_TO_POINTER(addr));
        return;
    }
    uint32_t last_idx = count - 1;
    __atomic_store_n(&shared_trace_data->prim_idx, last_idx,
                     __ATOMIC_RELAXED);
    if ((uint32_t)idx_to_remove < last_idx) {
        PrimitiveAccess *src = &shared_trace_data->primitives[last_idx];
        PrimitiveAccess *dst = &shared_trace_data->primitives[idx_to_remove];
        *dst = *src;
        OrderedMapEntry *moved_entry = ordered_map_lookup(g_read_access_tainted_primitives, dst->addr);
        if (moved_entry != NULL) {
            moved_entry->shared_index = idx_to_remove;
            moved_entry->data = dst;
        }
        memset(src, 0, sizeof(PrimitiveAccess));
    } else {
        memset(&shared_trace_data->primitives[idx_to_remove], 0,
               sizeof(PrimitiveAccess));
    }
    g_hash_table_remove(g_read_access_tainted_primitives->table, GSIZE_TO_POINTER(addr));
}

static SnapshotReadToken add_read_access_pointer(CPUArchState *env,
                                                 uintptr_t addr,
                                                 uintptr_t target,
                                                 uintptr_t pc,
                                                 const uint8_t *observed,
                                                 uint32_t observed_size) {
    SnapshotReadToken token = {0};
    if (shared_trace_data == NULL) return token;
    if (g_read_access_pointers == NULL) g_read_access_pointers = ordered_map_init(MAX_POINTER_ACCESS);
    OrderedMapEntry *entry = ordered_map_insert(g_read_access_pointers, addr, NULL);
    PointerAccess *ptr = NULL;
    if (entry->shared_index < 0) {
        uint32_t new_index;
        if (reserve_read_access_index(&shared_trace_data->ptr_idx,
                                      MAX_POINTER_ACCESS, &new_index)) {
            entry->shared_index = (int)new_index;
            ptr = &shared_trace_data->pointers[new_index];
        }
    } else if (entry->shared_index < MAX_POINTER_ACCESS) {
        ptr = &shared_trace_data->pointers[entry->shared_index];
    }
    if (ptr == NULL) {
        /* Sticky: typed consumption must not run on an over-cap record
         * set.  The generic mutation path still exits with the previous
         * behavior. */
        shared_trace_data->ptr_overflow = 1;
        trace_mem("[rpo] ptr shared_index error!!! %d\n", entry->shared_index);
        exit_with_status(1);
    }
    ptr->addr = addr;
    ptr->target = target;
    ptr->pc = pc;
    ptr->access_id = __atomic_fetch_add(&shared_trace_data->ptr_access_cnt, 1, __ATOMIC_RELAXED);
    ptr->run_epoch = shared_trace_data->run_epoch;
    ptr->expr = NULL;
    /* A replaced record never carries symbolic metadata from the
     * previous occupant: the event token that named it is invalid. */
    memset(ptr->observed_read_bytes, 0, sizeof(ptr->observed_read_bytes));
    ptr->observed_read_valid = 0;
    ptr->root_extension = SNAPSHOT_MUTATION_ROOT_IDENTITY;
    ptr->expr_index = -1;
    ptr->query_index = -1;
    /* The successful child load supplies the physical bytes.  They are copied
     * here, at record-write time, so a later finalization cannot be confused
     * by a rewritten cell. */
    if (observed != NULL && observed_size >= 1 &&
        observed_size <= sizeof(ptr->observed_read_bytes)) {
        memcpy(ptr->observed_read_bytes, observed, observed_size);
        ptr->observed_read_valid = 1;
    }
    /* Stage 7.1: refresh locators on every write so a replaced record
     * never carries a stale identity.  Capture failure leaves the
     * locator zeroed (valid == 0); the record stays generic-eligible. */
    memset(&ptr->cell, 0, sizeof(ptr->cell));
    memset(&ptr->target_ref, 0, sizeof(ptr->target_ref));
    if (osprey_collect_enabled && g_osprey_ctx != NULL) {
        osprey_capture_chunk_ref(env, (target_ulong)addr,
                                 (target_ulong)sizeof(target_ulong),
                                 &ptr->cell);
        if (target != 0) {
            osprey_capture_address_ref(env, (target_ulong)target,
                                       &ptr->target_ref);
        }
    }
    entry->data = ptr;
    trace_mem("[rpo] [addr %lx] [target %lx] [pc %lx] [index %d] [id %ld]\n",
              addr, target, pc, entry->shared_index, ptr->access_id);
    token.run_epoch = ptr->run_epoch;
    token.access_id = ptr->access_id;
    token.slot = (uint32_t)entry->shared_index;
    token.lane = SNAPSHOT_READ_LANE_POINTER;
    token.valid = 1;
    return token;
}

static SnapshotReadToken add_read_access_primitive(CPUArchState *env,
                                                   uintptr_t addr,
                                                   int size, uintptr_t pc,
                                                   const uint8_t *observed,
                                                   uint32_t observed_size) {
    SnapshotReadToken token = {0};
    if (shared_trace_data == NULL) return token;
    if (g_read_access_pointers) {
        uintptr_t aligned_addr = addr & ~(uintptr_t)0x07;
        OrderedMapEntry *ptr_entry = ordered_map_lookup(g_read_access_pointers, aligned_addr);
        if (ptr_entry != NULL) {
            remove_read_access_primitive(addr);
            return token;
        }
    }
    if (g_read_access_tainted_primitives == NULL) g_read_access_tainted_primitives = ordered_map_init(MAX_PRIMITIVE_ACCESS);
    PrimitiveAccess *prim = NULL;
    OrderedMapEntry *entry = ordered_map_insert(g_read_access_tainted_primitives, addr, NULL);
    if (entry->shared_index < 0) {
        uint32_t new_index;
        if (reserve_read_access_index(&shared_trace_data->prim_idx,
                                      MAX_PRIMITIVE_ACCESS, &new_index)) {
            entry->shared_index = (int)new_index;
            prim = &shared_trace_data->primitives[new_index];
        }
    } else if (entry->shared_index < MAX_PRIMITIVE_ACCESS) {
        prim = &shared_trace_data->primitives[entry->shared_index];
    }
    if (prim == NULL) {
        /* Sticky: see add_read_access_pointer. */
        shared_trace_data->prim_overflow = 1;
        trace_mem("[rpo] prim shared_index error!!! %d\n", entry->shared_index);
        exit_with_status(1);
    }
    prim->addr = addr;
    prim->size = size;
    prim->pc = pc;
    prim->access_id = __atomic_fetch_add(&shared_trace_data->prim_access_cnt, 1, __ATOMIC_RELAXED);
    prim->run_epoch = shared_trace_data->run_epoch;
    prim->expr = NULL;
    /* See add_read_access_pointer: a replaced record carries no symbolic
     * metadata, so a token captured from the previous occupant cannot be
     * finalized against it. */
    memset(prim->observed_read_bytes, 0, sizeof(prim->observed_read_bytes));
    prim->observed_read_valid = 0;
    prim->root_extension = SNAPSHOT_MUTATION_ROOT_IDENTITY;
    prim->expr_index = -1;
    prim->query_index = -1;
    /* See add_read_access_pointer: the successful child load supplies the
     * physical bytes at record-write time. */
    if (observed != NULL && observed_size >= 1 &&
        observed_size <= sizeof(prim->observed_read_bytes)) {
        memcpy(prim->observed_read_bytes, observed, observed_size);
        prim->observed_read_valid = 1;
    }
    /* Stage 7.1: refresh the cell locator (see add_read_access_pointer). */
    memset(&prim->cell, 0, sizeof(prim->cell));
    if (osprey_collect_enabled && g_osprey_ctx != NULL) {
        osprey_capture_chunk_ref(env, (target_ulong)addr,
                                 (target_ulong)size, &prim->cell);
    }
    entry->data = prim;
    trace_mem("[rpi] [addr %lx] [size %d] [pc %lx] [index %d] [id %ld]\n",
              addr, size, pc, entry->shared_index, prim->access_id);
    token.run_epoch = prim->run_epoch;
    token.access_id = prim->access_id;
    token.slot = (uint32_t)entry->shared_index;
    token.lane = SNAPSHOT_READ_LANE_PRIMITIVE;
    token.valid = 1;
    return token;
}

/* Finalize a retained read once the load's machine-width root expression and
 * the admitted BINRADAR_CONCRETIZATION query are both known.  Every field of
 * the token must still name the same record: a replacement, a lane change, an
 * LRU slot move, or a new run epoch makes the token stale and the caller
 * abstains.  The observed bytes stay as captured by the record writer. */
bool snapshot_finalize_read_token(SnapshotReadToken token,
                                  int64_t expr_index, int64_t query_index,
                                  SnapshotRootExtension root_extension) {
    if (!forkserver_installed || shared_trace_data == NULL || !token.valid ||
        expr_index < 0 || query_index < 0 ||
        (query_queue != NULL && next_query != NULL &&
         query_index >= (int64_t)(next_query - query_queue)) ||
        (root_extension != SNAPSHOT_ROOT_IDENTITY &&
         root_extension != SNAPSHOT_ROOT_ZEXT &&
         root_extension != SNAPSHOT_ROOT_SEXT)) {
        return false;
    }
    if (token.run_epoch != shared_trace_data->run_epoch) return false;

    if (token.lane == SNAPSHOT_READ_LANE_POINTER &&
        token.slot < MAX_POINTER_ACCESS) {
        PointerAccess *ptr = &shared_trace_data->pointers[token.slot];
        if (ptr->access_id == token.access_id &&
            ptr->run_epoch == token.run_epoch) {
            ptr->expr_index = expr_index;
            ptr->query_index = query_index;
            ptr->root_extension = (uint8_t)root_extension;
            return true;
        }
        return false;
    }
    if (token.lane == SNAPSHOT_READ_LANE_PRIMITIVE &&
        token.slot < MAX_PRIMITIVE_ACCESS) {
        PrimitiveAccess *prim = &shared_trace_data->primitives[token.slot];
        if (prim->access_id == token.access_id &&
            prim->run_epoch == token.run_epoch) {
            prim->expr_index = expr_index;
            prim->query_index = query_index;
            prim->root_extension = (uint8_t)root_extension;
            return true;
        }
    }
    return false;
}

bool is_valid_address(target_ulong addr, bool for_snapshot) {
    if (g_snapshot.pages == NULL) {
        trace_mem("ERROR! No valid pages\n");
        return false;
    }
    if (for_snapshot && g_hash_table_size(g_snapshot.pages) == 0) {
        return false;
    }
    target_ulong page = addr & SNAPSHOT_PAGE_MASK;
    SnapshotPageInfo *info = g_hash_table_lookup(g_snapshot.pages, GSIZE_TO_POINTER(page));
    if (info != NULL) {
        if (for_snapshot) {
            // Valid only if it has write permission
            return (info->perms & PAGE_WRITE) != 0;
        } else {
            return true;
        }
    }
    if (!for_snapshot) {
        return page_get_flags(addr) & PAGE_VALID;
    }
    return false;
}

// static GHashTable *get_pointer_access_table(void) {
//     if (g_pointer_access == NULL) {
//         g_pointer_access = g_hash_table_new_full(g_int64_hash, g_int64_equal, NULL, g_free);
//     }
//     return g_pointer_access;
// }

// static void access_pointer(target_ulong addr, target_ulong value, bool is_read) {
//     GHashTable *pointer_access = get_pointer_access_table();
//     if (is_read) {
//         trace_mem("%lx\n", (uintptr_t)pointer_access);
//     }
// }

static GArray *get_pending_allocs(void) {
    if (pending_allocs == NULL) {
        pending_allocs = g_array_new(FALSE, FALSE, sizeof(PendingAlloc));
    }
    return pending_allocs;
}

void snapshot_trace_pending_allocs(target_ulong size, target_ulong pc) {
    GArray *stack = get_pending_allocs();
    PendingAlloc alloc = {true, size, pc};
    g_array_append_val(stack, alloc);
    trace_mem("[alloc] [temp] [size %lx] [pc %lx]\n", size, pc);
}

PendingAlloc snapshot_trace_get_pending_allocs(target_ulong pc) {
    GArray *stack = get_pending_allocs();
    PendingAlloc result = {false, 0, 0};
    if (stack->len == 0) {
        // This should not happen
        return result;
    }
    result = g_array_index(stack, PendingAlloc, stack->len - 1);
    if (result.pc != pc) {
        result = (PendingAlloc){false, 0, 0};
        return result;
    }
    g_array_set_size(stack, stack->len - 1);
    return result;
}

static gint compare_regions(gconstpointer a, gconstpointer b, gpointer user_data) {
    const SnapshotMemRegion *ra = (const SnapshotMemRegion *)a;
    const SnapshotMemRegion *rb = (const SnapshotMemRegion *)b;
    if (ra->base < rb->base) return -1;
    if (ra->base > rb->base) return 1;
    return 0;
}

static gint compare_regions_ptr(gconstpointer a, gconstpointer b) {
    const SnapshotMemRegion *ra = *(const SnapshotMemRegion **)a;
    const SnapshotMemRegion *rb = *(const SnapshotMemRegion **)b;
    if (ra->base < rb->base) return -1;
    if (ra->base > rb->base) return 1;
    return 0;
}

static int check_addr_in_region(SnapshotMemRegion *mr, target_ulong addr) {
    if (mr->is_stack) {
        /* Stack grows downward: region is [base - size, base]. */
        if (mr->size != 0) {
            if (addr > mr->base) {
                return 1;
            }
            if (addr + mr->size >= mr->base) {
                return 0;
            }
            return -1;
        }

        /* size unknown: accept a lazy window below (or at) base */
        if (mr->base >= addr && mr->base - addr <= SNAPSHOT_STACK_LAZY_WINDOW) {
            return 0;
        }
        return (addr > mr->base) ? 1 : -1;
    }
    /* Heap/global regions are half-open: [base, base+size).  An access
     * exactly at base+size (one-past-end) is NOT inside. */
    if (mr->base + mr->size <= addr) return -1;
    if (mr->base > addr) return 1;
    return 0;
}

static target_ulong dyn_frame_low(const DynStackFrame *frame) {
    return frame ? frame->min_sp : 0;
}

static target_ulong dyn_frame_high(const DynStackFrame *frame) {
    return frame ? frame->entry_sp : 0;
}

static void dyn_frame_sync_region(DynStackFrame *frame) {
    if (frame == NULL) {
        return;
    }
    frame->region.is_heap = false;
    frame->region.is_stack = true;
    frame->region.base = frame->entry_sp;
    frame->region.size = frame->entry_sp >= frame->min_sp
        ? frame->entry_sp - frame->min_sp
        : 0;
    frame->region.pc = frame->frame_id;
}

static DynStackFrame *dyn_stack_top(void) {
    if (mr_manager.stack_data == NULL || mr_manager.stack_data->len == 0) {
        return NULL;
    }
    return g_array_index(mr_manager.stack_data, DynStackFrame *,
                         mr_manager.stack_data->len - 1);
}

static void dyn_stack_update_summary(void) {
    mr_manager.stack_region.is_heap = false;
    mr_manager.stack_region.is_stack = true;
    mr_manager.stack_region.pc = 0;

    if (mr_manager.stack_data == NULL || mr_manager.stack_data->len == 0) {
        mr_manager.stack_region.base = 0;
        mr_manager.stack_region.size = 0;
        return;
    }

    target_ulong high = 0;
    target_ulong low = (target_ulong)-1;
    for (guint i = 0; i < mr_manager.stack_data->len; i++) {
        DynStackFrame *frame = g_array_index(mr_manager.stack_data,
                                             DynStackFrame *, i);
        if (frame == NULL) {
            continue;
        }
        dyn_frame_sync_region(frame);
        if (frame->entry_sp > high) {
            high = frame->entry_sp;
        }
        if (frame->min_sp < low) {
            low = frame->min_sp;
        }
    }

    if (high == 0 || low == (target_ulong)-1 || low > high) {
        mr_manager.stack_region.base = 0;
        mr_manager.stack_region.size = 0;
        return;
    }
    mr_manager.stack_region.base = high;
    mr_manager.stack_region.size = high - low;
}

static bool dyn_frame_contains_access(const DynStackFrame *frame,
                                      target_ulong addr,
                                      target_ulong size) {
    if (frame == NULL || size == 0) {
        return false;
    }
    target_ulong end = addr + size;
    if (end < addr) {
        return false;
    }
    return addr >= dyn_frame_low(frame) && end <= dyn_frame_high(frame);
}

static bool dyn_frame_can_grow_for_access(const DynStackFrame *frame,
                                          target_ulong addr,
                                          target_ulong size) {
    if (frame == NULL || size == 0) {
        return false;
    }
    target_ulong end = addr + size;
    if (end < addr || end > frame->entry_sp || addr >= frame->min_sp) {
        return false;
    }
    return frame->min_sp - addr <= SNAPSHOT_STACK_LAZY_WINDOW;
}

static void dyn_stack_check_invariants(const char *where) {
    if (mr_manager.stack_data == NULL) {
        return;
    }

    for (guint i = 0; i < mr_manager.stack_data->len; i++) {
        DynStackFrame *frame = g_array_index(mr_manager.stack_data,
                                             DynStackFrame *, i);
        if (frame == NULL) {
            trace_mem("[stack-frame] [invariant-error] [where %s] "
                      "[depth %d] [reason null-frame]\n",
                      where ? where : "unknown", (int)i + 1);
            continue;
        }
        if (frame->frame_id == 0 || frame->min_sp > frame->entry_sp) {
            trace_mem("[stack-frame] [invariant-error] [where %s] "
                      "[fid %lx] [entry-sp %lx] [min-sp %lx] "
                      "[reason bad-frame-range]\n",
                      where ? where : "unknown",
                      (unsigned long)frame->frame_id, frame->entry_sp,
                      frame->min_sp);
        }

        if (i > 0) {
            DynStackFrame *caller = g_array_index(mr_manager.stack_data,
                                                  DynStackFrame *, i - 1);
            if (caller != NULL && caller->min_sp > frame->entry_sp) {
                trace_mem("[stack-frame] [invariant-error] [where %s] "
                          "[caller-fid %lx] [callee-fid %lx] "
                          "[caller-min-sp %lx] [callee-entry-sp %lx] "
                          "[reason caller-does-not-reach-call-sp]\n",
                          where ? where : "unknown",
                          (unsigned long)caller->frame_id,
                          (unsigned long)frame->frame_id,
                          caller->min_sp, frame->entry_sp);
            }
        }
    }
}

static void dyn_frame_grow_to_access(DynStackFrame *frame,
                                     target_ulong addr,
                                     target_ulong size,
                                     const char *reason) {
    if (frame == NULL) {
        return;
    }
    if (addr < frame->min_sp) {
        frame->min_sp = addr;
        frame->imprecise = true;
        dyn_frame_sync_region(frame);
        dyn_stack_update_summary();
        dyn_stack_check_invariants(reason);
        trace_mem("[stack-frame] [grow] [fid %lx] [addr %lx] [size %lx] "
                  "[entry-sp %lx] [min-sp %lx] [reason %s]\n",
                  (unsigned long)frame->frame_id, addr, size,
                  frame->entry_sp, frame->min_sp,
                  reason ? reason : "unknown");
    }
}

static void init_mr_manager(void) {
    mr_manager.stack_region.is_stack = true;
    if (mr_manager.stack_data == NULL) {
        mr_manager.stack_data = g_array_new(FALSE, FALSE, sizeof(DynStackFrame *));
    }
    if (mr_manager.heap_data == NULL) {
        mr_manager.heap_data = g_tree_new_full(
            (GCompareDataFunc)compare_regions,
            NULL,
            g_free,
            NULL
        );
        mr_manager.heap_cache_index = 0;
        for (int i = 0; i < SNAPSHOT_MEM_REG_CACHE; i++) {
            mr_manager.heap_cache[i] = NULL;
        }
    }
    if (mr_manager.global_data == NULL) {
        mr_manager.global_data = g_array_new(FALSE, FALSE, sizeof(SnapshotMemRegion *));
        mr_manager.global_cache_index = 0;
        for (int i = 0; i < SNAPSHOT_MEM_REG_CACHE; i++) {
            mr_manager.global_cache[i] = NULL;
        }
    }
}

static int mr_manager_search_cache(SnapshotMemRegion **mr_cache, target_ulong addr) {
    for (int i = 0; i < SNAPSHOT_MEM_REG_CACHE; i++) {
        SnapshotMemRegion *mr = mr_cache[i];
        if (mr != NULL && check_addr_in_region(mr, addr) == 0) {
            return i;
        }
    }
    return -1;
}

static int mr_manager_new_cache_index(int prev) {
    return (prev + 1) % SNAPSHOT_MEM_REG_CACHE;
}

static int mr_manager_search_cache_exact(SnapshotMemRegion **mr_cache, SnapshotMemRegion *query) {
    for (int i = 0; i < SNAPSHOT_MEM_REG_CACHE; i++) {
        SnapshotMemRegion *mr = mr_cache[i];
        if (mr != NULL && compare_regions(mr, query, NULL) == 0) {
            return i;
        }
    }
    return -1;
}

static void mr_manager_update_cache(SnapshotMemRegion **mr_cache, SnapshotMemRegion *target, int index) {
    if (index >= 0 && index < SNAPSHOT_MEM_REG_CACHE && mr_cache != NULL) {
        mr_cache[index] = target;
    }
}

static SnapshotMemRegion *mr_manager_get_cache(SnapshotMemRegion **mr_cache, int index) {
    if (index >= 0 && index < SNAPSHOT_MEM_REG_CACHE && mr_cache != NULL) {
        return mr_cache[index];
    }
    return NULL;
}

static void mr_manager_heap_insert(SnapshotMemRegion *mr) {
    g_tree_insert(mr_manager.heap_data, mr, mr);
}


static gint search_region(gconstpointer a, gconstpointer b) {
    const SnapshotMemRegion *region = (const SnapshotMemRegion *)a;
    const target_ulong addr = *(const target_ulong *)b;
    if (addr < region->base) return 1;
    if (addr >= region->base + region->size) return -1;
    return 0;
}

static SnapshotMemRegion *mr_manager_heap_search(target_ulong addr) {
    int query_result = mr_manager_search_cache(mr_manager.heap_cache, addr);
    SnapshotMemRegion *mr = mr_manager_get_cache(mr_manager.heap_cache, query_result);
    // Cache miss
    if (mr == NULL) {
        mr = g_tree_search(mr_manager.heap_data, (GCompareFunc)search_region, &addr);
    }
    if (mr == NULL) {
        // trace_mem("[mr] [heap] [error] failed to search region for [addr %lx]\n", addr);
        return NULL;
    }
    // Update cache
    int new_cache_index = mr_manager_new_cache_index(mr_manager.heap_cache_index);
    mr_manager_update_cache(mr_manager.heap_cache, mr, new_cache_index);
    mr_manager.heap_cache_index = new_cache_index;
    return mr;
}

void snapshot_trace_alloc(target_ulong base, target_ulong size, target_ulong pc) {
    trace_mem("[alloc] [start] [base %lx] [size %lx] [pc %lx]\n", base, size, pc);
    SnapshotMemRegion *obj = g_new(SnapshotMemRegion, 1);
    obj->is_heap = true;
    obj->is_stack = false;
    obj->base = base;
    obj->size = size;
    obj->pc = pc;
    mr_manager_heap_insert(obj);
}

void snapshot_trace_free(target_ulong base, target_ulong pc) {
    trace_mem("[free] [start] [base %lx] [pc %lx]\n", base, pc);
    SnapshotMemRegion query;
    query.base = base;
    query.pc = pc;

    /* Lazily initialize the quarantine queue. */
    if (heap_quarantine == NULL) {
        heap_quarantine = g_queue_new();
    }

    /* Remove from cache (same as mr_manager_heap_remove). */
    int query_result = SNAPSHOT_MEM_REG_CACHE;
    while (query_result >= 0) {
        query_result = mr_manager_search_cache_exact(mr_manager.heap_cache, &query);
        mr_manager_update_cache(mr_manager.heap_cache, NULL, query_result);
    }

    /* Steal (not remove) from the heap tree so the SnapshotMemRegion is
     * not freed by g_tree_remove's key-destroy callback.  If the region
     * is not found, there is nothing to quarantine. */
    SnapshotMemRegion *mr = g_tree_search(mr_manager.heap_data,
                                          (GCompareFunc)search_region, &base);
    if (mr != NULL) {
        g_tree_steal(mr_manager.heap_data, mr);
        g_queue_push_tail(heap_quarantine, mr);
        heap_quarantine_bytes += mr->size;
        trace_mem("[free] [quarantine] [base %lx] [size %lx] [pc %lx] [total %lu]\n",
                  base, mr->size, pc, heap_quarantine_bytes);

        /* Evict oldest entries until under the byte cap. */
        while (heap_quarantine_bytes > HEAP_QUARANTINE_MAX_BYTES &&
               !g_queue_is_empty(heap_quarantine)) {
            SnapshotMemRegion *old = g_queue_pop_head(heap_quarantine);
            if (old != NULL) {
                heap_quarantine_bytes -= old->size;
                g_free(old);
            }
        }
    } else {
        trace_mem("[free] [error] [base %lx] [pc %lx] not exist\n", base, pc);
    }
}

static SnapshotMemRegion *mr_manager_stack_search(target_ulong addr,
                                                   target_ulong size) {
    GArray *stack = mr_manager.stack_data;
    if (stack == NULL || stack->len == 0 || size == 0) {
        return NULL;
    }

    for (ssize_t i = stack->len - 1; i >= 0; i--) {
        DynStackFrame *frame = g_array_index(stack, DynStackFrame *, i);
        if (frame == NULL) {
            continue;
        }
        dyn_frame_sync_region(frame);
        if (dyn_frame_contains_access(frame, addr, size)) {
#ifdef SNAPSHOT_STACK_TRACE_VERBOSE
            int64_t off = (int64_t)addr - (int64_t)frame->entry_sp;
            trace_mem("[stack-frame] [lookup] [fid %lx] [addr %lx] "
                      "[off %ld] [size %lx] [depth %d]\n",
                      (unsigned long)frame->frame_id, addr, (long)off,
                      size, (int)i + 1);
#endif
            return &frame->region;
        }
    }

    DynStackFrame *top = dyn_stack_top();
    if (dyn_frame_can_grow_for_access(top, addr, size)) {
        dyn_frame_grow_to_access(top, addr, size, "access-below-min-sp");
#ifdef SNAPSHOT_STACK_TRACE_VERBOSE
        int64_t off = (int64_t)addr - (int64_t)top->entry_sp;
        trace_mem("[stack-frame] [lookup-fallback] [fid %lx] [addr %lx] "
                  "[off %ld] [size %lx] [depth %d]\n",
                  (unsigned long)top->frame_id, addr, (long)off,
                  size, stack->len);
#endif
        return &top->region;
    }

#ifdef SNAPSHOT_STACK_TRACE_VERBOSE
    trace_mem("[stack-frame] [lookup-miss] [addr %lx] [size %lx] [depth %d]\n",
              addr, size, stack->len);
#endif
    return NULL;
}

void snapshot_trace_stack_call(target_ulong sp, target_ulong call_pc,
                               target_ulong ret_pc) {
    if (mr_manager.stack_data == NULL) {
        init_mr_manager();
    }

    DynStackFrame *caller = dyn_stack_top();
    if (caller != NULL && sp < caller->min_sp) {
        dyn_frame_grow_to_access(caller, sp, 1, "call-sp-below-caller-min");
    }

    DynStackFrame *frame = g_new0(DynStackFrame, 1);
    frame->frame_id = next_dyn_frame_id++;
    frame->entry_sp = sp;
    frame->min_sp = sp >= sizeof(target_ulong) ? sp - sizeof(target_ulong) : 0;
    frame->call_pc = call_pc;
    frame->ret_pc = ret_pc;
    dyn_frame_sync_region(frame);

    g_array_append_val(mr_manager.stack_data, frame);
    dyn_stack_update_summary();
    dyn_stack_check_invariants("push");

    trace_mem("[stack-frame] [push] [fid %lx] [entry-sp %lx] [min-sp %lx] "
              "[call-pc %lx] [ret-pc %lx] [depth %d]\n",
              (unsigned long)frame->frame_id, frame->entry_sp, frame->min_sp,
              frame->call_pc, frame->ret_pc, mr_manager.stack_data->len);

    /* Stack region identity: the frame's site key (call PC, else ret PC,
     * else the dynamic frame id) is the canonical stack region id for
     * OSPREY. */
    target_ulong legacy_pc = frame->call_pc != 0 ? frame->call_pc : frame->ret_pc;
    if (legacy_pc == 0) {
        legacy_pc = frame->frame_id;
    }
    trace_mem("[stack] [push] [sp %lx] [size %lx] [pc %lx] [depth %d] "
              "[sr-base %lx] [sr-size %lx]\n",
              frame->entry_sp, frame->region.size, legacy_pc,
              mr_manager.stack_data->len, mr_manager.stack_region.base,
              mr_manager.stack_region.size);
}

void snapshot_trace_stack_ret(target_ulong sp, target_ulong actual_ret_pc) {
    if (mr_manager.stack_data == NULL) {
        init_mr_manager();
    }

    GArray *stack = mr_manager.stack_data;
    if (stack->len == 0) {
        trace_mem("[stack-frame] [ret-miss] [sp %lx] [ret-pc %lx] [depth 0]\n",
                  sp, actual_ret_pc);
        return;
    }

    DynStackFrame *frame = g_array_index(stack, DynStackFrame *, stack->len - 1);
    if (frame == NULL) {
        trace_mem("[stack-frame] [ret-error] [sp %lx] [ret-pc %lx] "
                  "[depth %d] [reason null-top]\n",
                  sp, actual_ret_pc, stack->len);
        return;
    }

    if (frame->ret_pc != 0 && frame->ret_pc != actual_ret_pc) {
        frame->imprecise = true;
        trace_mem("[stack-frame] [ret-mismatch] [fid %lx] [expected %lx] "
                  "[actual %lx] [sp %lx] [depth %d]\n",
                  (unsigned long)frame->frame_id, frame->ret_pc,
                  actual_ret_pc, sp, stack->len);
    }

    if (sp < frame->entry_sp) {
        frame->imprecise = true;
        trace_mem("[stack-frame] [ret-sp-mismatch] [fid %lx] "
                  "[entry-sp %lx] [sp %lx] [ret-pc %lx] "
                  "[reason stack-not-unwound-to-entry]\n",
                  (unsigned long)frame->frame_id, frame->entry_sp, sp,
                  actual_ret_pc);
    } else if (sp > frame->entry_sp) {
        trace_mem("[stack-frame] [ret-sp-adjust] [fid %lx] "
                  "[entry-sp %lx] [sp %lx] [ret-pc %lx] "
                  "[delta %lx]\n",
                  (unsigned long)frame->frame_id, frame->entry_sp, sp,
                  actual_ret_pc, sp - frame->entry_sp);
    }

    trace_mem("[stack-frame] [pop] [fid %lx] [sp %lx] [entry-sp %lx] "
              "[min-sp %lx] [ret-pc %lx] [imprecise %d] [depth %d]\n",
              (unsigned long)frame->frame_id, sp, frame->entry_sp,
              frame->min_sp, actual_ret_pc, frame->imprecise,
              stack->len - 1);
    target_ulong legacy_pc = frame->call_pc != 0 ? frame->call_pc : frame->ret_pc;
    if (legacy_pc == 0) {
        legacy_pc = frame->frame_id;
    }
    trace_mem("[stack] [pop] [sp %lx] [base %lx] [pc %lx] [depth %d]\n",
              sp, frame->entry_sp, legacy_pc, stack->len - 1);

    g_array_set_size(stack, stack->len - 1);
    g_free(frame);
    dyn_stack_update_summary();
    dyn_stack_check_invariants("pop");
}

void snapshot_trace_stack_push(target_ulong sp, target_ulong pc) {
    snapshot_trace_stack_call(sp, 0, pc);
}

void snapshot_trace_stack_pop(target_ulong sp) {
    snapshot_trace_stack_ret(sp, 0);
}

void snapshot_trace_global_add(target_ulong base, target_ulong size, target_ulong pc, const char *name) {
    if (mr_manager.global_data == NULL) {
        init_mr_manager();
    }
    SnapshotMemRegion *mr = g_new(SnapshotMemRegion, 1);
    mr->is_heap = false;
    mr->is_stack = false;
    mr->base = base;
    mr->size = size;
    mr->pc = pc;

    g_array_append_val(mr_manager.global_data, mr);
    
    g_array_sort(mr_manager.global_data, (GCompareFunc)compare_regions_ptr);
    
    trace_mem("[global] [add] [base %lx] [size %lx] [name %s] [pc %lx]\n", 
              base, size, name ? name : "unknown", pc);
}

static SnapshotMemRegion *mr_manager_global_search(target_ulong addr) {
    // trace_mem("[mr] [global] [search] [addr %lx]\n", addr);

    int query_result = mr_manager_search_cache(mr_manager.global_cache, addr);
    SnapshotMemRegion *mr = mr_manager_get_cache(mr_manager.global_cache, query_result);
    if (mr != NULL) {
        return mr;
    }

    GArray *globals = mr_manager.global_data;
    if (globals->len == 0) return NULL;

    int low = 0;
    int high = globals->len - 1;
    SnapshotMemRegion *found = NULL;

    // Binary search
    while (low <= high) {
        int mid = low + (high - low) / 2;
        SnapshotMemRegion *mr = g_array_index(globals, SnapshotMemRegion *, mid);

        int res = check_addr_in_region(mr, addr);
        if (res == 0) {
            found = mr;
            break;
        } else if (res < 0) { // mr->base + size < addr
            low = mid + 1;
        } else { // mr->base > addr
            high = mid - 1;
        }
    }

    if (found) {
        int next_cache_idx = mr_manager_new_cache_index(mr_manager.global_cache_index);
        mr_manager_update_cache(mr_manager.global_cache, found, next_cache_idx);
        mr_manager.global_cache_index = next_cache_idx;
        return found;
    }

    // trace_mem("[mr] [global] [error] failed to search region for [addr %lx]\n", addr);
    return NULL;
}

SnapshotMemRegion *snapshot_mem_region_search_with_size(target_ulong addr,
                                                        target_ulong size) {
    SnapshotMemRegion *mr = mr_manager_stack_search(addr, size);
    if (mr != NULL) {
        return mr;
    }

    mr = mr_manager_global_search(addr);
    if (mr != NULL) {
        return mr;
    }

    mr = mr_manager_heap_search(addr);
    if (mr != NULL) {
        return mr;
    }
    return NULL;
}

SnapshotMemRegion *snapshot_mem_region_search(target_ulong addr) {
    return snapshot_mem_region_search_with_size(addr, 1);
}

/* Check whether a memory access is within bounds of a known heap
 * allocation.
 *   MEMCHECK_OK        — access is within a valid heap region, or to
 *                        stack/global/unmapped memory (handled by MMU).
 *   MEMCHECK_HEAP_OOB  — access starts inside a heap region but extends
 *                        past its recorded end (exact-bounds overrun).
 *
 * Only exact-bounds overruns are reported. We deliberately do NOT
 * flag accesses that merely fall *near* (but outside) a recorded region:
 * the region tree is built from PLT-call-site malloc/free hooks and can
 * miss regions allocated through un-modelled entry points or by libraries,
 * so a "near a known region" heuristic produces false OOB reports on
 * accesses that actually belong to an adjacent, untracked allocation.
 * (This was the source of the pre-entrypoint memcheck crashes that broke
 * 23/30 benchmark subjects.) */
MemcheckResult snapshot_memcheck_access(target_ulong addr, target_ulong size) {
    /* UNKNOWN provenance: exact-bounds fallback on LIVE objects only.
     * Do NOT report UAF from numeric quarantine — UNKNOWN provenance
     * cannot distinguish a stale pointer from a valid pointer to a
     * reused or untracked allocation at the same address.  Provenance
     * identity, not address history, is required for UAF (§7). */
    SnapshotMemRegion *mr = mr_manager_heap_search_pub(addr);
    if (mr != NULL) {
        /* Half-open containment: mr->base <= addr < region_end.
         * The tree search guarantees this, so region_end - addr is
         * well-defined (no wrap).  Access is OOB when its full interval
         * exceeds the region end. */
        target_ulong region_end = mr->base + mr->size;
        if (region_end >= mr->base &&
            addr < region_end &&
            (uint64_t)size > (uint64_t)(region_end - addr)) {
            return MEMCHECK_HEAP_OOB;
        }
    }
    return MEMCHECK_OK;
}

/* Runtime helper called from instrumented TCG code (non-symbolic mode).
 * Routes through the provenance checker with an UNKNOWN tag; the
 * provenance checker applies the exact-bounds fallback on LIVE objects
 * and records a non-fatal pending finding (deferred crash policy, §8).
 * This helper must NOT call _exit(): the raw-TCG pass inserts it AFTER the
 * guest memory op (so a real fault raises first, §4/§9), and it must not
 * terminate execution itself.  The finding is finalized at guest exit. */
void snapshot_memcheck_helper(target_ulong addr, target_ulong size, target_ulong pc) {
    if (!binradar_memcheck_enabled) return;
    if (symbolic_start_code > 0 && (pc < symbolic_start_code || pc >= symbolic_end_code)) {
        return;
    }
    CPUState *cpu = thread_cpu;
    CPUArchState *env = cpu ? cpu->env_ptr : NULL;
    if (!env) return;
    PtrTag unknown_tag = {0};
    /* The finding is recorded as non-fatal (pending).  Do not _exit here:
     * the raw-TCG pass inserts this helper AFTER the qemu_ld/st, so a
     * faulting access has already raised before this helper runs (§4/§9).
     * The deferred finalize path converts pending findings to synthetic
     * crashes at guest exit. */
    provenance_check_access(env, addr, size, pc, unknown_tag, -1, 0);
}

/* Forward declaration: defined in tcg/symbolic/symbolic.c */
void memcheck_init(void);

bool snapshot_is_taken(void) {
    // return g_snapshot.is_snapshot_taken;
    return true;
}

void snapshot_init(void) {
    memset(&mr_manager, 0, sizeof(SnapshotMemRegionManager));
    next_dyn_frame_id = 1;
    init_mr_manager();
    memset(&g_snapshot, 0, sizeof(SnapshotState));
    g_snapshot.pages = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
    g_snapshot.is_snapshot_taken = false;
    // g_snapshot.cpu_state = malloc(sizeof(CPUArchState));
    // memset(g_snapshot.cpu_state, 0, sizeof(CPUArchState));
    size_t shm_size = sizeof(SharedTraceData);
    shared_trace_data = mmap(NULL, shm_size, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (shared_trace_data == MAP_FAILED) {
        log_msg("mmap shared memory failed");
        exit_with_status(1);
    }
    memset(shared_trace_data, 0, shm_size);
    /* Load binradar env vars early so binradar_memcheck_enabled is set
     * before any memory access instrumentation runs. */
    snapshot_load_binradar_env();
    /* Initialize PLT hooks for memcheck-only mode. */
    memcheck_init();
    /* OSPREY: parse config; when enabled, allocate the shared run and
     * arm the translator-side collection flag. */
    if (g_osprey_ctx == NULL) {
        OspreyConfig osprey_config;
        if (osprey_config_from_env(&osprey_config)) {
            g_osprey_ctx = osprey_new(&osprey_config);
            osprey_collect_enabled = osprey_config.enabled ? 1 : 0;
        } else {
            /* Keep forkserver startup and generic mutation fallback alive, but
             * make a rejected OSPREY configuration observable. */
            log_msg("[osprey] [config] [disabled] [reason parse-failure]\n");
        }
    }
    if (g_osprey_ctx != NULL && g_osprey_ctx->config.enabled &&
        g_osprey_shared_run == NULL) {
        size_t run_size = osprey_shared_run_size(&g_osprey_ctx->config);
        void *run_mem = mmap(NULL, run_size, PROT_READ | PROT_WRITE,
                             MAP_SHARED | MAP_ANONYMOUS, -1, 0);
        if (run_mem == MAP_FAILED) {
            log_msg("[osprey] [fatal] shared run mmap failed\n");
            exit_with_status(1);
        }
        g_osprey_shared_run = run_mem;
        osprey_shared_run_reset(g_osprey_shared_run, 0,
                                &g_osprey_ctx->config);
        osprey_child_use_shared_run(g_osprey_ctx, g_osprey_shared_run);
        log_msg("[osprey] [init] [shared-mb %zu] [run-bytes %zu]\n",
                g_osprey_ctx->config.shared_bytes / (1024u * 1024u),
                run_size);
    }
    /* Deferred provenance findings live in the shared mmap so the parent
     * can read them after waitpid even on timeout/SIGKILL. */
    provenance_set_shared_fault_ptr(&shared_trace_data->prov_pending_fault);
    provenance_init();
}

static int walk_memory_cb(void *priv, target_ulong start, target_ulong end,
                          unsigned long flags) {
    if (flags & PAGE_READ) {
        target_ulong addr;
        for (addr = start; addr < end; addr += SNAPSHOT_PAGE_SIZE) {
            SnapshotPageInfo *info = g_malloc0(sizeof(SnapshotPageInfo));
            info->addr = addr;
            info->perms = flags;
            info->data = g_malloc(SNAPSHOT_PAGE_SIZE);
            uint64_t key = addr & SNAPSHOT_PAGE_MASK;

            void *host_addr = g2h(addr);
            // memcpy(info->data, host_addr, SNAPSHOT_PAGE_SIZE);

            g_hash_table_insert(g_snapshot.pages, GSIZE_TO_POINTER(key), info);
            trace_mem("[snapshot] [memwalk] [addr %lx] [perms %ld] [host %lx]\n", (uint64_t)addr, flags, (uint64_t)host_addr);
        }
    }
    return 0;
}

void snapshot_save(void) {
    if (g_snapshot.pages == NULL) snapshot_init();
    if (g_snapshot.is_snapshot_taken) return;
    log_msg("[snapshot] [mem] [start]\n");
    // CPU state
    // if (g_snapshot.cpu_state) {
    //     trace_mem("[snapshot] [cpu] [at %lx] [size %ld]\n", (uintptr_t)cpu, sizeof(CPUArchState));
    //     memcpy(g_snapshot.cpu_state, cpu, sizeof(CPUArchState));
    // }
    // Memory
    walk_memory_regions(&g_snapshot, walk_memory_cb);

    g_snapshot.start_brk = target_brk;
    g_snapshot.start_mmap = mmap_next_start;
    
    g_snapshot.is_snapshot_taken = true;
    log_msg("[snapshot] [result] [brk %llx] [mmap %llx] [pages %d]\n", (long long int)target_brk, (long long int)mmap_next_start, g_hash_table_size(g_snapshot.pages));
    dump_coverage_edge_log(false);

    /* OSPREY Stage 2.1: freeze the pre-snapshot prefix.  Every fact
     * collected before the snapshot (entrypoint frame, init-time
     * frames) becomes the frozen prefix family; the baseline child
     * contributes the post-snapshot suffix.  The merge treats
     * `prefix ∪ baseline-child` as exactly one unmodified sample.
     * Idempotent: snapshot_save runs once. */
    if (g_osprey_ctx != NULL && g_osprey_shared_run != NULL &&
        g_osprey_ctx->config.enabled) {
        osprey_shared_run_freeze_prefix(g_osprey_ctx, g_osprey_shared_run);
    }
}

void snapshot_write_access(SnapshotMemAccess *mem_access) {
    if (!forkserver_installed) return;
    uint64_t addr = mem_access->addr;
    uint64_t size = mem_access->size;
    if (size == sizeof(target_ulong)) {
        target_ulong target;
        memcpy(&target, mem_access->target, sizeof(target_ulong));
    }
    // target_ulong start = addr & SNAPSHOT_PAGE_MASK;
    // target_ulong end = (addr + size - 1) & SNAPSHOT_PAGE_MASK;
    trace_mem("[snapshot] [waccess] [mem] [addr %lx] [size %ld]\n", addr, size);
}

SnapshotReadToken snapshot_read_access(CPUArchState *env, SnapshotMemAccess *mem_access) {
    SnapshotReadToken none = {0};
    if (!forkserver_installed) return none;
    uintptr_t addr = mem_access->addr;
    uintptr_t size = mem_access->size;
    /* The successful child load supplies the physical bytes.  A caller that
     * did not populate them (out-of-range or oversized access) leaves the
     * observation invalid rather than reporting stale target bytes. */
    const uint8_t *observed = NULL;
    uint32_t observed_size = 0;
    if (mem_access->observed_valid && size >= 1 &&
        size <= sizeof(mem_access->target)) {
        observed = mem_access->target;
        observed_size = (uint32_t)size;
    }
    if (size == sizeof(target_ulong)) {
        target_ulong target;
        memcpy(&target, mem_access->target, sizeof(target_ulong));
        if (is_valid_address(target, true)) {
            // Add to pointer
            SnapshotReadToken token = add_read_access_pointer(
                env, addr, target, mem_access->pc, observed, observed_size);
            trace_mem("[snapshot] [raccess] [pointer] [addr %lx] [target %lx] [pc %lx]\n", addr, target, mem_access->pc);
            return token;
        } else if (target == 0) {
            // It may be a null pointer
            SnapshotReadToken token = add_read_access_primitive(
                env, addr, size, mem_access->pc, observed, observed_size);
            trace_mem("[snapshot] [raccess] [null-pointer] [addr %lx] [pc %lx]\n", addr, mem_access->pc);
            return token; // Do not add it twice
        } else {
            trace_mem("[snapshot] [raccess] [primitive] [addr %lx] [value %lx] [pc %lx]\n", addr, target, mem_access->pc);
        }
    }
    if (mem_access->symbolic_value) {
        // Tainted value
        SnapshotReadToken token = add_read_access_primitive(
            env, addr, size, mem_access->pc, observed, observed_size);
        trace_mem("[snapshot] [raccess] [mem] [addr %lx] [size %ld]\n", addr, size);
        return token;
    }
    trace_mem("[snapshot] [raccess] [mem] [addr %lx] [size %ld]\n", addr, size);
    return none;
}

// Unused: replaced by fork server
// void snapshot_restore(CPUArchState *cpu) {
//     // CPU state
//     restoring_to_snapshot = true;
//     if (g_snapshot.cpu_state) {
//         trace_mem("[snapshot] [restore-cpu]\n");
//         memcpy(cpu, g_snapshot.cpu_state, sizeof(CPUArchState));
//     }
    
//     SnapshotTLS *tls = get_tls_w();
//     // mmap
//     while (g_snapshot.new_mappings != NULL) {
//         SnapshotMapping *map = (SnapshotMapping *)g_snapshot.new_mappings->data;
//         // Remove new mmap
//         trace_mem("[snapshot] [restore] [munmap] [addr %lx]\n", map->start);
//         target_munmap(map->start, map->len);
//         g_free(map);
//         g_snapshot.new_mappings = g_list_delete_link(g_snapshot.new_mappings, g_snapshot.new_mappings);
//     }

//     // brk
//     // The heap has shrunk - restore missing pages
//     if (target_brk < g_snapshot.start_brk) {
//         target_ulong aligned_new_brk = (target_brk + (SNAPSHOT_PAGE_SIZE - 1)) & (~(SNAPSHOT_PAGE_SIZE - 1));
//         trace_mem("[snapshot] [restore] [brk-s] [snap %lx] [new %lx] [aligned %lx] [size %lx]\n", target_brk, g_snapshot.start_brk, aligned_new_brk, g_snapshot.start_brk - aligned_new_brk);
//         abi_long brk_ret = do_brk(g_snapshot.start_brk);
//         if (brk_ret != g_snapshot.start_brk) {
//             trace_mem("[snapshot] [restore] [brk-s-err] [grow-failed %lx]\n", brk_ret);
//         }
//     } else if (target_brk > g_snapshot.start_brk) { // Remove new allocations
//         trace_mem("[snapshot] [restore] [brk-l] [snap %lx] [new %lx]\n", target_brk, g_snapshot.start_brk);
//     }

//     // 3. Dirty Page
//     GHashTableIter iter;
//     gpointer key, value;
//     g_hash_table_iter_init(&iter, tls->dirty_pages);

//     while (g_hash_table_iter_next(&iter, &key, &value)) {
//         target_ulong addr = *(target_ulong*)key;

//         SnapshotPageInfo *info = g_hash_table_lookup(g_snapshot.pages, &addr);
//         if (info) {
//             // memcpy with original data
//             void *host_addr = g2h(addr);

//             // mprotect(host_addr, SNAPSHOT_PAGE_SIZE, PROT_READ | PROT_WRITE); 
//             memcpy(host_addr, info->data, SNAPSHOT_PAGE_SIZE);
//             trace_mem("[snapshot] [restore] [dirty] [addr %lx]\n", (uintptr_t)addr);
//         } else {
//             // void *host_addr = g2h(addr);
//             // memset(host_addr, 0, SNAPSHOT_PAGE_SIZE);
//             trace_mem("[snapshot] [restore] [dirty-unknown] [addr %lx]\n", (uintptr_t)addr);
//         }
//     }

//     g_hash_table_remove_all(tls->dirty_pages);
//     for(int i=0; i<4; i++) tls->access_cache[i] = -1;
    
//     trace_mem("[snapshot] [restore] [fin]\n");
//     fflush(stderr);
// }

// Syscall Hook
static target_ulong last_brk_end;  /* previous brk end (for shrink detection) */
void snapshot_syscall(CPUArchState *env, uintptr_t syscall_no,
                      uintptr_t syscall_arg0, uintptr_t syscall_arg1,
                      uintptr_t syscall_arg2, uintptr_t syscall_arg3,
                      uintptr_t syscall_arg4, uintptr_t syscall_arg5,
                      uintptr_t syscall_arg6, uintptr_t ret_val) {
    switch (syscall_no) {
    case TARGET_NR_read:
    case TARGET_NR_pread64: // read from file (write to buffer)
        // read(fd, buf, count) -> read count
        if ((long)ret_val > 0) {
            // addr
            SnapshotMemAccess mem_access = {
                .symbolic_addr = false,
                .symbolic_value = false,
                .addr = syscall_arg1,
                .pc = 0,
                .target = {0},
                .ptr = NULL,
                .size = ret_val
            };
            if (ret_val <= 8) {
                void *buf = g2h(syscall_arg1);
                memcpy(mem_access.target, buf, ret_val);
            }
            snapshot_write_access(&mem_access);
            /* Provenance: kernel wrote into the buffer — stale shadow
             * entries must not be reloaded (FIX_TRACER.md test 18). */
            sem_mem_overwrite(env, syscall_arg1, ret_val, SEM_OP_SYSCALL);
        }
        break;
    case TARGET_NR_write:
    case TARGET_NR_pwrite64: // write to file (read from buffer)
        if ((long)ret_val > 0) {
            SnapshotMemAccess mem_access = {
                .symbolic_addr = false,
                .symbolic_value = false,
                .observed_valid = false,
                .addr = syscall_arg1,
                .pc = 0,
                .target = {0},
                .ptr = NULL,
                .size = ret_val
            };
            if (ret_val <= 8) {
                void *buf = g2h(syscall_arg1);
                memcpy(mem_access.target, buf, ret_val);
                mem_access.observed_valid = true;
            }
            (void)snapshot_read_access(env, &mem_access);
        }
        break;
#if defined(TARGET_NR_futex)
    case TARGET_NR_futex: // Fast user mutex
        // futex(uaddr, op, val, timeout, uaddr2, val3)
        // This QEMU version implements WAIT/WAKE/REQUEUE/CMP_REQUEUE and
        // WAKE_OP only.  Of those, only WAKE_OP writes guest memory: its
        // encoded atomic operation updates the 32-bit word at uaddr2.
        if ((long)ret_val >= 0) {
            uint32_t op = (uint32_t)syscall_arg1 & FUTEX_CMD_MASK;
            if (op == FUTEX_WAKE_OP) {
                if (syscall_arg4) {
                    sem_mem_overwrite(env, syscall_arg4, sizeof(uint32_t), SEM_OP_SYSCALL);
                }
            }
        }
        break;
#endif
#if defined(TARGET_NR_newfstatat)
    case TARGET_NR_newfstatat: // newfstatat(dirfd, pathname, statbuf, flags)
        // Kernel wrote sizeof(struct target_stat) bytes on success only.
        if ((long)ret_val == 0) {
            sem_mem_overwrite(env, syscall_arg2, sizeof(struct target_stat), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_fstatat64)
    case TARGET_NR_fstatat64:
        if ((long)ret_val == 0) {
            sem_mem_overwrite(env, syscall_arg2, sizeof(struct target_stat64), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_stat) || defined(TARGET_NR_lstat) || defined(TARGET_NR_fstat)
    case TARGET_NR_stat:
    case TARGET_NR_lstat:
    case TARGET_NR_fstat:
        // stat(pathname, statbuf) / lstat / fstat(fd, statbuf)
        if ((long)ret_val == 0) {
            sem_mem_overwrite(env, syscall_arg1, sizeof(struct target_stat), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_statx)
    case TARGET_NR_statx: // statx(dirfd, pathname, flags, mask, statxbuf)
        if ((long)ret_val == 0) {
            sem_mem_overwrite(env, syscall_arg4, sizeof(struct target_statx), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_statfs) || defined(TARGET_NR_fstatfs)
    case TARGET_NR_statfs:
    case TARGET_NR_fstatfs:
        // statfs(path, buf) / fstatfs(fd, buf)
        if ((long)ret_val == 0) {
            sem_mem_overwrite(env, syscall_arg1, sizeof(struct target_statfs), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_readlink)
    case TARGET_NR_readlink: // readlink(pathname, buf, bufsiz)
        // Kernel wrote ret bytes (the link length, no NUL).
        if ((long)ret_val > 0) {
            sem_mem_overwrite(env, syscall_arg1, ret_val, SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_readlinkat)
    case TARGET_NR_readlinkat: // readlinkat(dirfd, pathname, buf, bufsiz)
        if ((long)ret_val > 0) {
            sem_mem_overwrite(env, syscall_arg2, ret_val, SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_getrandom)
    case TARGET_NR_getrandom: // getrandom(buf, buflen, flags)
        if ((long)ret_val > 0) {
            sem_mem_overwrite(env, syscall_arg0, ret_val, SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_gettimeofday)
    case TARGET_NR_gettimeofday: // gettimeofday(tv, tz)
        // QEMU's linux-user implementation writes only the timeval and
        // deliberately passes NULL for the obsolete timezone argument.
        if ((long)ret_val == 0) {
            if (syscall_arg0) {
                sem_mem_overwrite(env, syscall_arg0,
                                         sizeof(struct target_timeval), SEM_OP_SYSCALL);
            }
        }
        break;
#endif
#if defined(TARGET_NR_clock_gettime)
    case TARGET_NR_clock_gettime: // clock_gettime(clockid, tp)
        // Kernel wrote struct timespec on success only.
        if ((long)ret_val == 0 && syscall_arg1) {
            sem_mem_overwrite(env, syscall_arg1,
                                     sizeof(struct target_timespec), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_clock_getres)
    case TARGET_NR_clock_getres: // clock_getres(clockid, res)
        if ((long)ret_val == 0 && syscall_arg1) {
            sem_mem_overwrite(env, syscall_arg1,
                                     sizeof(struct target_timespec), SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_getdents)
    case TARGET_NR_getdents: // getdents(fd, dirp, count)
        // Kernel wrote ret bytes of dirent records into dirp.
        if ((long)ret_val > 0) {
            sem_mem_overwrite(env, syscall_arg1, ret_val, SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_getdents64)
    case TARGET_NR_getdents64: // getdents64(fd, dirp, count)
        // Kernel wrote ret bytes of dirent records into dirp.
        if ((long)ret_val > 0) {
            sem_mem_overwrite(env, syscall_arg1, ret_val, SEM_OP_SYSCALL);
        }
        break;
#endif
#if defined(TARGET_NR_recvfrom)
    case TARGET_NR_recvfrom: // recvfrom(fd, buf, len, flags, src_addr, addrlen)
        // Handled exactly at the copy-out site in do_recvfrom() (payload,
        // returned sockaddr, and the in/out addrlen word).  No-op here so
        // the source hook is the single owner of socket invalidation.
        break;
#endif
#if defined(TARGET_NR_recvmsg)
    case TARGET_NR_recvmsg: // recvmsg(fd, msg, flags)
        // Handled exactly at the copy-out site in do_sendrecvmsg_locked()
        // (payload iovecs, msg_name, control data, and the returned
        // msg_namelen/msg_controllen/msg_flags header fields).  No-op here.
        break;
#endif
    case TARGET_NR_brk: // heap adjustment
        // brk(new_brk_addr)
        // Handled in snapshot_restore
        trace_mem("New brk %lx received.\n", syscall_arg0);
        // On shrink (new brk below the previous end), stale shadow tags
        // in the unmapped tail must not be reloaded after regrowth.
        if ((long)ret_val < (long)last_brk_end) {
            sem_mem_overwrite(env, ret_val, last_brk_end - ret_val, SEM_OP_MAPPING);
        }
        last_brk_end = ret_val;
        break;
    // System call that changes heap shape:
    case TARGET_NR_mmap: // Memory map to file
        // mmap(addr, size, prot, flags, fd, offset) -> mapped addr
        snapshot_add_mapping(ret_val, syscall_arg1);
        // A fresh mapping must never inherit stale shadow entries (an
        // address previously used by another object).
        if ((long)ret_val > 0) {
            sem_mem_overwrite(env, ret_val, syscall_arg1, SEM_OP_MAPPING);
        }
        break;
    case TARGET_NR_mremap: // memory remap
        // mremap(old_addr, old_size, new_size, flags, new_addr) -> new addr
        // snapshot_remove_mapping(syscall_arg0, syscall_arg1);
        snapshot_add_mapping(ret_val, syscall_arg2);
        // Old range's shadow entries are stale (pages may be moved/freed).
        if ((long)ret_val >= 0) {
            sem_mem_overwrite(env, syscall_arg0, syscall_arg1, SEM_OP_MAPPING);
            if ((uintptr_t)ret_val != (uintptr_t)syscall_arg0) {
                sem_mem_overwrite(env, ret_val, syscall_arg2, SEM_OP_MAPPING);
            }
        }
        break;
    case TARGET_NR_munmap: // unmap
        // munmap(addr, length)
        // snapshot_remove_mapping(syscall_arg0, syscall_arg1);
        // Invalidate shadow for the unmapped range (stale tags must not
        // survive an address-space reuse).
        if ((long)ret_val == 0) {
            sem_mem_overwrite(env, syscall_arg0, syscall_arg1, SEM_OP_MAPPING);
        }
        break;
    case TARGET_NR_mprotect: // permission
        // mprotect(start, len, prot)
        // BINRADAR TODO: implement
        break;
    default:
        break;
    }
}

// Syscall Hook: munmap (linux-user/syscall.c do_syscall1())
// Do not unmap if any page in the range is in the snapshot
int snapshot_is_unmap_allowed(target_ulong addr, target_ulong len) {
    return 1;
    target_ulong end = addr + len;
    for (target_ulong p = addr; p < end; p += SNAPSHOT_PAGE_SIZE) {
        if (g_hash_table_contains(g_snapshot.pages, GSIZE_TO_POINTER(p & SNAPSHOT_PAGE_MASK))) {
            return 0; // False
        }
    }
    return 1; // True
}


void snapshot_add_mapping(target_ulong addr, target_ulong len) {
    if (addr == -1) return;
    SnapshotMapping *map = g_malloc(sizeof(SnapshotMapping));
    map->start = addr;
    map->len = len;
    g_snapshot.new_mappings = g_list_prepend(g_snapshot.new_mappings, map);
    trace_mem("[snapshot] [mmap] [add] [addr %lx] [len %ld]\n", addr, len);
}

void snapshot_remove_mapping(target_ulong addr, target_ulong len) {
    for (GList *l = g_snapshot.new_mappings; l != NULL; l = l->next) {
        SnapshotMapping *map = (SnapshotMapping *)l->data;
        g_free(map);
        trace_mem("[snapshot] [munmap] [remove] [addr %lx]\n", addr);
        return;
    }
}

void snapshot_fork_setup(void) {
    log_msg("[forkserver] [setup]\n");
}

/* Stage 7.4 owns fresh-target mapping/application.  The mapping request is
 * exactly the decoded aggregate extent; only the accepted payload interval
 * receives an OSPREY overwrite event. */
static target_ulong snapshot_alloc_pointer_target(CPUArchState *env,
                                                  uint64_t extent)
    G_GNUC_UNUSED;
static target_ulong snapshot_alloc_pointer_target(CPUArchState *env,
                                                  uint64_t extent)
{
    abi_long mapped;
    target_ulong target;

    (void)env;
    if (extent == 0 || extent > SNAPSHOT_PAGE_SIZE) {
        return (target_ulong)-1;
    }
    mapped = target_mmap(0, (abi_ulong)extent,
                         PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS,
                         -1, 0);
    if (mapped == -1) {
        log_msg("[mod-pointer] [alloc-error] target_mmap failed\n");
        return (target_ulong)-1;
    }
    target = (target_ulong)(abi_ulong)mapped;
    if (target == 0 || (uint64_t)(abi_ulong)target != (uint64_t)(abi_ulong)mapped) {
        log_msg("[mod-pointer] [alloc-error] target address is not representable\n");
        return (target_ulong)-1;
    }
    log_msg("[mod-pointer] [alloc] [addr %lx] [size %llu]\n",
            target, (unsigned long long)extent);
    return target;
}

static bool snapshot_test_parse_offset(const char *text, uint64_t *out)
{
    char *end = NULL;
    uint64_t value;

    if (text == NULL || text[0] == '\0' || out == NULL) {
        return false;
    }
    errno = 0;
    value = g_ascii_strtoull(text, &end, 0);
    if (errno != 0 || end == text || *end != '\0') {
        return false;
    }
    *out = value;
    return true;
}

static bool snapshot_test_address_ref_equal(
    const OspreyRuntimeAddressRef *a, const OspreyRuntimeAddressRef *b)
{
    OspreyKey a_key;
    OspreyKey b_key;

    if (a == NULL || b == NULL) {
        return false;
    }
    a_key = osprey_addr_key(&a->address);
    b_key = osprey_addr_key(&b->address);
    return osprey_key_equal(&a_key, &b_key) && a->raw == b->raw &&
           a->instance_id == b->instance_id &&
           a->prov_object_id == b->prov_object_id &&
           a->prov_generation == b->prov_generation &&
           a->valid == b->valid;
}

static bool snapshot_test_install_applied_model(void)
{
    const char *enabled = getenv("BINRADAR_OSPREY_TEST_APPLIED_STATE");
    const char *pointer_offset_text =
        getenv("BINRADAR_OSPREY_TEST_POINTER_GLOBAL_OFFSET");
    const char *null_offset_text =
        getenv("BINRADAR_OSPREY_TEST_NULL_GLOBAL_OFFSET");
    const char *late_offset_text =
        getenv("BINRADAR_OSPREY_TEST_LATE_POINTER_GLOBAL_OFFSET");
    const char *generic_offset_text =
        getenv("BINRADAR_OSPREY_TEST_GENERIC_GLOBAL_OFFSET");
    PointerAccess *selected = NULL;
    PointerAccess *selected_late = NULL;
    PrimitiveAccess *selected_null = NULL;
    PrimitiveAccess *selected_generic = NULL;
    OspreyRuntimeAddressRef *target_ref;
    OspreyRegionInstance *target_instance = NULL;
    OspreyMutationModel *model;
    OspreyMutationEntry *entries;
    uint64_t pointer_offset = 0;
    uint64_t null_offset = 0;
    uint64_t late_offset = 0;
    uint64_t generic_offset = 0;
    uint32_t entry_count;
    uint32_t same_site_instances = 0;
    uint64_t target_extent = 13;

    if (enabled == NULL || enabled[0] == '\0' || atoi(enabled) == 0 ||
        g_osprey_ctx == NULL || shared_trace_data == NULL) {
        return false;
    }
    if (!snapshot_test_parse_offset(pointer_offset_text, &pointer_offset) ||
        !snapshot_test_parse_offset(null_offset_text, &null_offset) ||
        !snapshot_test_parse_offset(late_offset_text, &late_offset) ||
        !snapshot_test_parse_offset(generic_offset_text, &generic_offset)) {
        log_msg("[osprey] [test-model] [invalid-symbol-offsets]\n");
        return false;
    }
    for (uint32_t i = 0; i < shared_trace_data->ptr_idx &&
                           i < MAX_POINTER_ACCESS; i++) {
        PointerAccess *candidate = &shared_trace_data->pointers[i];
        uint64_t offset;

        if (candidate->cell.start.valid != 1 ||
            candidate->target_ref.valid != 1 ||
            candidate->cell.start.address.region.kind !=
                OSPREY_REGION_GLOBAL) {
            continue;
        }
        offset = (uint64_t)candidate->cell.start.address.offset;
        if (offset == pointer_offset) {
            selected = candidate;
        } else if (offset == late_offset) {
            selected_late = candidate;
        }
    }
    if (selected == NULL || selected_late == NULL ||
        !snapshot_test_address_ref_equal(&selected->target_ref,
                                         &selected_late->target_ref)) {
        log_msg("[osprey] [test-model] [missing-pointer-access]\n");
        return false;
    }
    for (uint32_t i = 0; i < shared_trace_data->prim_idx &&
                           i < MAX_PRIMITIVE_ACCESS; i++) {
        PrimitiveAccess *candidate = &shared_trace_data->primitives[i];
        uint64_t offset;

        if (candidate->size != sizeof(target_ulong) ||
            candidate->cell.start.valid != 1 ||
            candidate->cell.start.address.region.kind !=
                OSPREY_REGION_GLOBAL) {
            continue;
        }
        offset = (uint64_t)candidate->cell.start.address.offset;
        if (offset == null_offset) {
            selected_null = candidate;
        } else if (offset == generic_offset) {
            selected_generic = candidate;
        }
    }
    if (selected_null == NULL || selected_generic == NULL) {
        log_msg("[osprey] [test-model] [missing-primitive-access]\n");
        return false;
    }
    target_ref = &selected->target_ref;
    for (guint i = 0; i < g_osprey_ctx->region_instances->len; i++) {
        OspreyRegionInstance *candidate = &g_array_index(
            g_osprey_ctx->region_instances, OspreyRegionInstance, i);
        OspreyKey candidate_region = osprey_region_key(&candidate->region);
        OspreyKey target_region = osprey_region_key(
            &target_ref->address.region);

        if (!osprey_key_equal(&candidate_region, &target_region)) {
            continue;
        }
        same_site_instances++;
        if (candidate->instance_id == target_ref->instance_id &&
            candidate->raw_base <= target_ref->raw &&
            target_ref->raw < candidate->raw_max &&
            candidate->prov_object_id == target_ref->prov_object_id &&
            candidate->prov_generation == target_ref->prov_generation) {
            target_instance = candidate;
        }
    }
    if (target_instance == NULL || same_site_instances < 2 ||
        target_ref->address.region.kind != OSPREY_REGION_HEAP_SITE ||
        target_ref->raw != target_instance->raw_base ||
        target_ref->address.offset != 0 ||
        target_instance->raw_max - target_ref->raw < target_extent) {
        log_msg("[osprey] [test-model] [missing-target-instance]\n");
        return false;
    }

    entry_count = 3;
    model = g_new0(OspreyMutationModel, 1);
    entries = g_new0(OspreyMutationEntry, entry_count);
    if (model == NULL || entries == NULL) {
        g_free(entries);
        g_free(model);
        return false;
    }
    const OspreyRuntimeChunkRef *cells[3] = {
        &selected->cell, &selected_late->cell, &selected_null->cell,
    };
    for (uint32_t i = 0; i < entry_count; i++) {
        entries[i].cell.address = cells[i]->start.address;
        entries[i].cell.size = sizeof(target_ulong);
        entries[i].target_base = target_ref->address;
        entries[i].extent = target_extent;
        entries[i].support = 1;
        entries[i].kind = OSPREY_MUTATION_AGGREGATE_STRUCT;
    }
    for (uint32_t i = 1; i < entry_count; i++) {
        OspreyMutationEntry value = entries[i];
        uint32_t j = i;
        while (j > 0 && value.cell.address.offset <
                          entries[j - 1].cell.address.offset) {
            entries[j] = entries[j - 1];
            j--;
        }
        entries[j] = value;
    }
    for (uint32_t i = 0; i < entry_count; i++) entries[i].ordinal = i;
    model->version = OSPREY_MUTATION_MODEL_VERSION;
    model->entry_count = entry_count;
    model->publication_valid = 1;
    model->entries = entries;
    if (g_osprey_ctx->model != NULL) {
        osprey_model_free(g_osprey_ctx->model);
        g_osprey_ctx->model = NULL;
    }
    if (g_osprey_ctx->staged_model != NULL) {
        osprey_model_free(g_osprey_ctx->staged_model);
        g_osprey_ctx->staged_model = NULL;
    }
    osprey_mutation_model_clear(g_osprey_ctx);
    g_osprey_ctx->mutation_model = model;
    g_osprey_ctx->mutation_model_ready = true;
    g_osprey_ctx->mutation_runtime_ready = false;
    g_osprey_ctx->tx_status = OSPREY_OK;
    g_osprey_ctx->tx_stage = NULL;
    g_osprey_ctx->tx_reason = NULL;
    g_osprey_ctx->tx_model_ready = true;
    log_msg("[osprey] [test-model] [cell %lx] [late-cell %lx] "
            "[null-cell %lx] [generic-cell %lx] [target %lx] "
            "[extent %llu] [same-site %u]\n",
            (unsigned long)selected->cell.start.raw,
            (unsigned long)selected_late->cell.start.raw,
            (unsigned long)selected_null->cell.start.raw,
            (unsigned long)selected_generic->cell.start.raw,
            (unsigned long)target_ref->raw,
            (unsigned long long)target_extent, same_site_instances);
    return true;
}

static bool snapshot_apply_fresh_target(CPUArchState *env,
                                        target_ulong target,
                                        const uint8_t *bytes,
                                        uint64_t extent) G_GNUC_UNUSED;
static bool snapshot_apply_fresh_target(CPUArchState *env,
                                        target_ulong target,
                                        const uint8_t *bytes,
                                        uint64_t extent)
{
    if (env == NULL || target == 0 || bytes == NULL || extent == 0 ||
        extent > SNAPSHOT_PAGE_SIZE) {
        return false;
    }
    memcpy(g2h(target), bytes, (size_t)extent);
    sem_mem_overwrite(env, target, (target_ulong)extent,
                      SEM_OP_SNAPSHOT);
    return true;
}

/* Stage 7.5 test-only observation.  The file is opt-in, append-only, and
 * outside the forkserver protocol; production runs never open it.  Keep the
 * record fixed-width and address-bearing only for the concrete child state,
 * never host pointers or model identities. */
static uint64_t snapshot_test_observation_digest(const uint8_t *bytes,
                                                 uint64_t size)
{
    uint64_t digest = 1469598103934665603ULL;
    for (uint64_t i = 0; i < size; i++) {
        digest ^= bytes[i];
        digest *= 1099511628211ULL;
    }
    return digest;
}

static void snapshot_test_observe_write(const SnapshotMutationWrite *write,
                                        target_ulong fresh_target,
                                        target_ulong before_value,
                                        bool applied)
{
    const char *path = getenv("BINRADAR_OSPREY_TEST_OBSERVATION_FILE");
    const uint8_t *observed_target = NULL;
    uint8_t cell_bytes[sizeof(target_ulong)] = {0};
    uint64_t observed_extent = 0;
    uint64_t digest = 0;
    target_ulong cell_value = 0;
    uint8_t first = 0;
    uint8_t last = 0;
    int fd;

    if (path == NULL || path[0] == '\0' || write == NULL) return;
    if (applied && fresh_target != 0 && write->target.extent != 0) {
        observed_target = g2h(fresh_target);
        observed_extent = write->target.extent;
    } else if (applied && write->target.resolved_end >
                              write->target.resolved_raw) {
        observed_target = g2h((target_ulong)write->target.resolved_raw);
        observed_extent = write->target.resolved_end -
                          write->target.resolved_raw;
    }
    if (observed_target != NULL) {
        digest = snapshot_test_observation_digest(observed_target,
                                                   observed_extent);
        first = observed_target[0];
        last = observed_target[observed_extent - 1];
    }
    if (applied) {
        size_t cell_size = MIN((size_t)write->size, sizeof(cell_bytes));
        if (write->addr < SNAPSHOT_PAGE_SIZE) {
            memcpy(cell_bytes, write->value, cell_size);
        } else {
            memcpy(cell_bytes, g2h(write->addr), cell_size);
        }
        memcpy(&cell_value, cell_bytes, sizeof(cell_value));
    }
    fd = open(path, O_WRONLY | O_CREAT | O_APPEND, 0600);
    if (fd < 0) return;
    dprintf(fd,
            "[stage7-observation] [status %s] [kind %u] [cell %lx] "
            "[before %lx] [value %lx] [target %lx] [extent %llu] "
            "[digest %016llx] [first %02x] [last %02x] "
            "[resolved_raw %lx] [resolved_end %lx]\n",
            applied ? "ok" : "apply-failure", (unsigned)write->kind,
            (unsigned long)write->addr, (unsigned long)before_value,
            (unsigned long)cell_value, (unsigned long)fresh_target,
            (unsigned long long)observed_extent,
            (unsigned long long)digest, first, last,
            (unsigned long)write->target.resolved_raw,
            (unsigned long)write->target.resolved_end);
    close(fd);
}

static int64_t snapshot_expr_index_from_ptr(const Expr *expr)
{
    uintptr_t base;
    uintptr_t end;
    uintptr_t value;

    if (expr == NULL || pool == NULL || next_free_expr == NULL) {
        return -1;
    }
    base = (uintptr_t)pool;
    end = (uintptr_t)next_free_expr;
    value = (uintptr_t)expr;
    if (value < base || value >= end ||
        ((value - base) % sizeof(Expr)) != 0) {
        return -1;
    }
    return (int64_t)((value - base) / sizeof(Expr));
}

static SnapshotMutationPlan *snapshot_mutation_new_descriptor(
    target_ulong addr, uint32_t size, int64_t expr_index,
    int64_t query_index, SnapshotMutationKind kind, const uint8_t *value,
    uint64_t target_extent, const uint8_t *target_bytes)
{
    if (size == 0 || size > sizeof(((SnapshotMutationWrite *)0)->value)) {
        return NULL;
    }
    switch (kind) {
    case SNAPSHOT_MUTATION_BYTES:
    case SNAPSHOT_MUTATION_POINTER_NULL:
    case SNAPSHOT_MUTATION_POINTER_OOB:
    case SNAPSHOT_MUTATION_POINTER_FRESH:
        break;
    default:
        return NULL;
    }
    if (addr < SNAPSHOT_PAGE_SIZE && addr >= CPU_NB_REGS) {
        return NULL;
    }
    if (kind != SNAPSHOT_MUTATION_BYTES && size != sizeof(target_ulong)) {
        return NULL;
    }
    if (kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
        if (target_extent == 0 || target_extent > SNAPSHOT_PAGE_SIZE ||
            target_bytes == NULL || target_extent > SIZE_MAX) {
            return NULL;
        }
    } else if (target_extent != 0 || target_bytes != NULL) {
        return NULL;
    }

    SnapshotMutationPlan *plan = snapshot_mutation_try_malloc0(sizeof(*plan));
    if (plan == NULL) {
        return NULL;
    }
    plan->num_mods = 1;
    plan->mods = snapshot_mutation_try_malloc0(sizeof(*plan->mods));
    if (plan->mods == NULL) {
        snapshot_mutation_free(plan);
        return NULL;
    }

    SnapshotMutationWrite *write = &plan->mods[0];
    write->kind = kind;
    write->addr = addr;
    write->size = size;
    write->expr_index = expr_index;
    write->query_index = query_index;
    if (value != NULL) {
        memcpy(write->value, value, sizeof(write->value));
    }

    if (kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
        write->target.extent = target_extent;
        write->target.bytes = snapshot_mutation_try_malloc(
            (size_t)target_extent);
        if (write->target.bytes == NULL) {
            snapshot_mutation_free(plan);
            return NULL;
        }
        memcpy(write->target.bytes, target_bytes, (size_t)target_extent);
    }
    return plan;
}

static SnapshotMutationPlan *snapshot_mutation_new(
    const MutationCandidate *candidate, SnapshotMutationKind kind,
    const uint8_t *value, uint32_t size, uint64_t target_extent,
    const uint8_t *target_bytes)
{
    if (candidate == NULL) {
        return NULL;
    }
    const uint8_t *source_value = value != NULL ? value : candidate->value;
    return snapshot_mutation_new_descriptor(
        (target_ulong)candidate->addr, size,
        snapshot_expr_index_from_ptr(candidate->expr), -1, kind,
        source_value, target_extent, target_bytes);
}

static bool snapshot_mutation_enqueue_plan_array(
    GQueue *queue, SnapshotMutationPlan **plans, size_t count)
{
    if (queue == NULL || plans == NULL || count == 0 ||
        count > SIZE_MAX / sizeof(GList *)) {
        snapshot_mutation_free_batch(plans, count);
        return false;
    }

    GList **links = snapshot_mutation_try_malloc0(count * sizeof(*links));
    if (links == NULL) {
        snapshot_mutation_free_batch(plans, count);
        return false;
    }
    for (size_t i = 0; i < count; i++) {
        if (plans[i] == NULL) {
            for (size_t j = 0; j < i; j++) g_list_free_1(links[j]);
            g_free(links);
            snapshot_mutation_free_batch(plans, count);
            return false;
        }
        links[i] = snapshot_mutation_try_list_alloc();
        if (links[i] == NULL) {
            for (size_t j = 0; j < i; j++) g_list_free_1(links[j]);
            g_free(links);
            snapshot_mutation_free_batch(plans, count);
            return false;
        }
        links[i]->data = plans[i];
    }

    /* All links and plan ownership are complete before queue mutation. */
    for (size_t i = 0; i < count; i++) {
        g_queue_push_tail_link(queue, links[i]);
        plans[i] = NULL;
    }
    g_free(links);
    return true;
}

static bool snapshot_mutation_enqueue_batch(GQueue *queue,
                                             SnapshotMutationPlan **plans,
                                             uint32_t count)
{
    return snapshot_mutation_enqueue_plan_array(queue, plans, count);
}

static bool snapshot_mutation_enqueue_one(GQueue *queue,
                                           SnapshotMutationPlan *plan)
{
    SnapshotMutationPlan *batch[] = {plan};
    return snapshot_mutation_enqueue_batch(queue, batch, 1);
}

/* Per-advisor family quota.  Advisor 1 is compact OSPREY and advisor 2 is
 * symbolic boundary advice; each gets its own 4,096 slots so an advisor can
 * never consume another advisor's allocation.  The combined cap is the sum,
 * which keeps mode `off` byte-identical for OSPREY: a disabled advisor
 * reserves nothing and the OSPREY quota is unchanged. */
#define SNAPSHOT_MUTATION_MAX_SPECIALIZED_FAMILIES 4096u
#define SNAPSHOT_MUTATION_MAX_COMBINED_FAMILIES 8192u
#define SNAPSHOT_MUTATION_MAX_SPECIALIZED_VARIANTS 64u
#define SNAPSHOT_MUTATION_MAX_SPECIALIZED_WRITES 64u

/* Families already admitted for one advisor, counted over accepted copies.
 * Duplicate descriptors are not counted because they are not admitted. */
static uint32_t snapshot_mutation_advisor_family_count(
    const SnapshotMutationCoordinator *coordinator, uint32_t advisor_id)
{
    uint32_t count = 0;
    if (coordinator == NULL || coordinator->families == NULL) return 0;
    for (guint i = 0; i < coordinator->families->len; i++) {
        const SnapshotMutationProposalFamily *family =
            g_ptr_array_index(coordinator->families, i);
        if (family->advisor_id == advisor_id) count++;
    }
    return count;
}

static bool snapshot_mutation_token_equal(
    SnapshotMutationSourceToken a, SnapshotMutationSourceToken b)
{
    return a.run_epoch == b.run_epoch &&
           a.source_ordinal == b.source_ordinal;
}

static const SnapshotMutationBaselineEntry *snapshot_mutation_lookup_entry(
    const SnapshotMutationBaseline *baseline,
    SnapshotMutationSourceToken token)
{
    const SnapshotMutationBaselineEntry *entry;

    if (baseline == NULL || baseline->entries == NULL ||
        token.run_epoch != baseline->run_epoch ||
        token.source_ordinal >= baseline->entry_count) {
        return NULL;
    }
    entry = &baseline->entries[token.source_ordinal];
    return snapshot_mutation_token_equal(entry->token, token) ? entry : NULL;
}

static void snapshot_mutation_proposal_family_free(gpointer data)
{
    SnapshotMutationProposalFamily *family = data;
    if (family == NULL) return;
    if (family->variants != NULL) {
        for (uint32_t vi = 0; vi < family->variant_count; vi++) {
            SnapshotMutationProposalVariant *variant = &family->variants[vi];
            if (variant->writes != NULL) {
                for (uint32_t wi = 0; wi < variant->write_count; wi++) {
                    g_free((void *)variant->writes[wi].target_bytes);
                }
                g_free(variant->writes);
            }
        }
        g_free(family->variants);
    }
    g_free(family);
}

static bool snapshot_mutation_memory_interval(
    const SnapshotMutationBaselineEntry *entry, uint32_t size,
    uint64_t *end_out)
{
    uint64_t end;
    if (entry == NULL || size == 0 || entry->addr < SNAPSHOT_PAGE_SIZE) {
        return false;
    }
    if ((uint64_t)entry->addr > UINT64_MAX - size) return false;
    end = (uint64_t)entry->addr + size;
    if (end <= (uint64_t)entry->addr) return false;
    if (end_out != NULL) *end_out = end;
    return true;
}

static bool snapshot_mutation_proposal_validate(
    const SnapshotMutationCoordinator *coordinator,
    const SnapshotMutationProposalFamily *family)
{
    const SnapshotMutationBaselineEntry *primary;
    const bool observed_read =
        family != NULL &&
        family->seed_semantics == SNAPSHOT_MUTATION_SEED_OBSERVED_READ;

    if (coordinator == NULL || coordinator->baseline == NULL ||
        family == NULL || family->advisor_id == 0 ||
        family->variants == NULL || family->variant_count == 0 ||
        family->variant_count > SNAPSHOT_MUTATION_MAX_SPECIALIZED_VARIANTS ||
        (family->seed_semantics != SNAPSHOT_MUTATION_SEED_SNAPSHOT_STATE &&
         !observed_read)) {
        return false;
    }
    primary = snapshot_mutation_lookup_entry(coordinator->baseline,
                                             family->primary_seed);
    if (primary == NULL || !primary->typed_eligible || primary->protected_addr) {
        return false;
    }
    /* An observed-read family proposes values synthesized from the bytes the
     * baseline child actually loaded.  Without a finalized observation there
     * is no source of truth to lower a candidate through, so the whole family
     * is rejected rather than silently falling back to generic semantics. */
    if (observed_read &&
        (!primary->observed_read_valid ||
         (primary->size != 1 && primary->size != 2 &&
          primary->size != 4 && primary->size != sizeof(target_ulong)) ||
         primary->lane != SNAPSHOT_MUTATION_LANE_PRIMITIVE)) {
        return false;
    }

    for (uint32_t vi = 0; vi < family->variant_count; vi++) {
        const SnapshotMutationProposalVariant *variant = &family->variants[vi];
        uint32_t primary_count = 0;
        if (variant->writes == NULL || variant->write_count == 0 ||
            variant->write_count > SNAPSHOT_MUTATION_MAX_SPECIALIZED_WRITES) {
            return false;
        }
        for (uint32_t prior_vi = 0; prior_vi < vi; prior_vi++) {
            if (family->variants[prior_vi].variant_id == variant->variant_id) {
                return false;
            }
        }
        for (uint32_t wi = 0; wi < variant->write_count; wi++) {
            const SnapshotMutationProposalWrite *write = &variant->writes[wi];
            const SnapshotMutationBaselineEntry *entry =
                snapshot_mutation_lookup_entry(coordinator->baseline,
                                               write->destination);
            uint64_t begin_a = 0, end_a = 0;
            if (entry == NULL || !entry->typed_eligible || entry->protected_addr ||
                write->size == 0 ||
                write->size > sizeof(write->value) ||
                (entry->addr >= SNAPSHOT_PAGE_SIZE &&
                 !snapshot_mutation_memory_interval(entry, write->size,
                                                    &end_a))) {
                return false;
            }
            if (observed_read && write->kind != SNAPSHOT_MUTATION_BYTES) {
                return false;
            }
            if (wi > 0 &&
                variant->writes[wi - 1].destination.source_ordinal >=
                    write->destination.source_ordinal) {
                return false;
            }
            if (snapshot_mutation_token_equal(write->destination,
                                              family->primary_seed)) {
                primary_count++;
                if (write->size != primary->size) return false;
                if (observed_read) {
                    /* Boundary advice rewrites observed scalar memory with a
                     * synthesized scalar.  A pointer-family write would
                     * replace compact OSPREY's ownership of pointer
                     * alternatives, and the value must differ from both the
                     * physical baseline bytes and the bytes the child
                     * actually read, or the child would observe no change. */
                    if (write->kind != SNAPSHOT_MUTATION_BYTES) return false;
                    if (memcmp(write->value, primary->observed_read_bytes,
                               write->size) == 0) {
                        return false;
                    }
                }
                if (write->kind != SNAPSHOT_MUTATION_POINTER_FRESH &&
                    memcmp(write->value, primary->planner_bytes,
                           write->size) == 0) {
                    return false;
                }
                if (write->kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
                    for (uint32_t bi = 0; bi < primary->size; bi++) {
                        if (primary->planner_bytes[bi] != 0) return false;
                    }
                }
            }
            switch (write->kind) {
            case SNAPSHOT_MUTATION_BYTES:
                if (write->target_extent != 0 || write->target_bytes != NULL ||
                    memcmp(write->value, entry->planner_bytes,
                           write->size) == 0) {
                    return false;
                }
                break;
            case SNAPSHOT_MUTATION_POINTER_NULL:
            case SNAPSHOT_MUTATION_POINTER_OOB:
                if (entry->size != sizeof(target_ulong) ||
                    write->size != sizeof(target_ulong) ||
                    write->target_extent != 0 || write->target_bytes != NULL ||
                    memcmp(write->value, entry->planner_bytes,
                           write->size) == 0) {
                    return false;
                }
                break;
            case SNAPSHOT_MUTATION_POINTER_FRESH:
                if (entry->size != sizeof(target_ulong) ||
                    write->size != sizeof(target_ulong) ||
                    write->target_extent == 0 ||
                    write->target_extent > SNAPSHOT_PAGE_SIZE ||
                    write->target_bytes == NULL) {
                    return false;
                }
                break;
            default:
                return false;
            }
            if (entry->addr < SNAPSHOT_PAGE_SIZE) {
                if (entry->addr >= CPU_NB_REGS) return false;
                for (uint32_t other = 0; other < wi; other++) {
                    const SnapshotMutationProposalWrite *previous =
                        &variant->writes[other];
                    const SnapshotMutationBaselineEntry *previous_entry =
                        snapshot_mutation_lookup_entry(
                            coordinator->baseline, previous->destination);
                    if (previous_entry != NULL &&
                        previous_entry->addr == entry->addr) {
                        return false;
                    }
                }
            } else {
                for (uint32_t other = 0; other < wi; other++) {
                    const SnapshotMutationProposalWrite *previous =
                        &variant->writes[other];
                    const SnapshotMutationBaselineEntry *previous_entry =
                        snapshot_mutation_lookup_entry(
                            coordinator->baseline, previous->destination);
                    uint64_t begin_b, end_b;
                    if (previous_entry == NULL ||
                        previous_entry->addr < SNAPSHOT_PAGE_SIZE ||
                        !snapshot_mutation_memory_interval(previous_entry,
                                                          previous->size,
                                                          &end_b)) {
                        continue;
                    }
                    begin_a = (uint64_t)entry->addr;
                    begin_b = (uint64_t)previous_entry->addr;
                    if (begin_a < end_b && begin_b < end_a) return false;
                }
            }
        }
        if (primary_count != 1) return false;
    }
    return true;
}

static SnapshotMutationProposalFamily *snapshot_mutation_proposal_copy(
    const SnapshotMutationProposalFamily *source)
{
    SnapshotMutationProposalFamily *copy;

    if (source == NULL) return NULL;
    copy = snapshot_mutation_try_malloc0(sizeof(*copy));
    if (copy == NULL) return NULL;
    *copy = *source;
    copy->variants = snapshot_mutation_try_malloc0(
        (size_t)source->variant_count * sizeof(*copy->variants));
    if (copy->variants == NULL) {
        snapshot_mutation_proposal_family_free(copy);
        return NULL;
    }
    for (uint32_t vi = 0; vi < source->variant_count; vi++) {
        const SnapshotMutationProposalVariant *src = &source->variants[vi];
        SnapshotMutationProposalVariant *dst = &copy->variants[vi];
        *dst = *src;
        dst->writes = snapshot_mutation_try_malloc0(
            (size_t)src->write_count * sizeof(*dst->writes));
        if (dst->writes == NULL) {
            snapshot_mutation_proposal_family_free(copy);
            return NULL;
        }
        for (uint32_t wi = 0; wi < src->write_count; wi++) {
            const SnapshotMutationProposalWrite *src_write = &src->writes[wi];
            SnapshotMutationProposalWrite *dst_write = &dst->writes[wi];
            *dst_write = *src_write;
            dst_write->target_bytes = NULL;
            if (src_write->kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
                if (src_write->target_bytes == NULL ||
                    src_write->target_extent == 0 ||
                    src_write->target_extent > SIZE_MAX) {
                    snapshot_mutation_proposal_family_free(copy);
                    return NULL;
                }
                uint8_t *payload = snapshot_mutation_try_malloc(
                    (size_t)src_write->target_extent);
                if (payload == NULL) {
                    snapshot_mutation_proposal_family_free(copy);
                    return NULL;
                }
                memcpy(payload, src_write->target_bytes,
                       (size_t)src_write->target_extent);
                dst_write->target_bytes = payload;
            }
        }
    }
    return copy;
}

static bool snapshot_mutation_proposal_same_descriptor(
    const SnapshotMutationProposalFamily *a,
    const SnapshotMutationProposalFamily *b)
{
    if (a == NULL || b == NULL || a->advisor_id != b->advisor_id ||
        a->family_id != b->family_id ||
        !snapshot_mutation_token_equal(a->primary_seed, b->primary_seed) ||
        a->seed_semantics != b->seed_semantics ||
        a->variant_count != b->variant_count) {
        return false;
    }
    for (uint32_t vi = 0; vi < a->variant_count; vi++) {
        const SnapshotMutationProposalVariant *av = &a->variants[vi];
        const SnapshotMutationProposalVariant *bv = &b->variants[vi];
        if (av->variant_id != bv->variant_id ||
            av->write_count != bv->write_count) return false;
        for (uint32_t wi = 0; wi < av->write_count; wi++) {
            const SnapshotMutationProposalWrite *aw = &av->writes[wi];
            const SnapshotMutationProposalWrite *bw = &bv->writes[wi];
            if (!snapshot_mutation_token_equal(aw->destination,
                                               bw->destination) ||
                aw->kind != bw->kind || aw->size != bw->size ||
                memcmp(aw->value, bw->value, sizeof(aw->value)) != 0 ||
                aw->target_extent != bw->target_extent ||
                aw->resolved_raw != bw->resolved_raw ||
                aw->resolved_end != bw->resolved_end) return false;
            if (aw->target_extent != 0 &&
                (aw->target_bytes == NULL || bw->target_bytes == NULL ||
                 memcmp(aw->target_bytes, bw->target_bytes,
                        (size_t)aw->target_extent) != 0)) return false;
        }
    }
    return true;
}

bool snapshot_mutation_sink_submit(
    SnapshotMutationProposalSink *sink,
    const SnapshotMutationProposalFamily *family)
{
    SnapshotMutationProposalFamily *copy;
    if (sink == NULL || sink->coordinator == NULL || family == NULL ||
        family->advisor_id != sink->advisor_id ||
        family->advisor_priority != sink->advisor_priority ||
        sink->coordinator->families == NULL ||
        sink->coordinator->families->len >=
            SNAPSHOT_MUTATION_MAX_COMBINED_FAMILIES ||
        snapshot_mutation_advisor_family_count(sink->coordinator,
                                               sink->advisor_id) >=
            SNAPSHOT_MUTATION_MAX_SPECIALIZED_FAMILIES ||
        !snapshot_mutation_proposal_validate(sink->coordinator, family)) {
        return false;
    }
    for (guint i = 0; i < sink->coordinator->families->len; i++) {
        SnapshotMutationProposalFamily *existing =
            g_ptr_array_index(sink->coordinator->families, i);
        if (snapshot_mutation_proposal_same_descriptor(existing, family)) {
            return true;
        }
    }
    copy = snapshot_mutation_proposal_copy(family);
    if (copy == NULL) return false;
    g_ptr_array_add(sink->coordinator->families, copy);
    return true;
}

static void snapshot_mutation_baseline_free(
    SnapshotMutationBaseline *baseline)
{
    if (baseline == NULL) return;
    g_free(baseline->entries);
    g_free(baseline);
}

static void snapshot_mutation_coordinator_clear(
    SnapshotMutationCoordinator *coordinator)
{
    if (coordinator == NULL) return;
    if (coordinator->families != NULL) {
        g_ptr_array_free(coordinator->families, TRUE);
        coordinator->families = NULL;
    }
    if (coordinator->staged != NULL) {
        g_ptr_array_free(coordinator->staged, TRUE);
        coordinator->staged = NULL;
    }
    coordinator->baseline = NULL;
}

/* Modify guest program's state based on mod_manager. */
static void mod_manager_init(SnapshotExitInfo *exit_info)
{
    if (mod_manager == NULL && !mutation_analysis_started) {
        mod_manager = g_new0(ModificationManager, 1);
        mod_manager->modifications = g_queue_new();
        mod_manager->current = NULL;
        mutation_analysis_started = true;
        /* Directed-mode query-window preservation is the only consumer that
         * needs pool pointers.  Reconstruct them from the child's scalar
         * cursors after validating both indexes; an unusable cursor drops the
         * window request instead of publishing a partially valid range. */
        int64_t query_cursor = snapshot_query_cursor_index(exit_info);
        int64_t expr_cursor = snapshot_expr_cursor_index(exit_info);
        if (query_queue != NULL && pool != NULL &&
            snapshot_query_cursor_valid(query_cursor) &&
            snapshot_expr_cursor_valid(expr_cursor)) {
            snapshot_dump_query_window(query_queue + query_cursor,
                                       pool + expr_cursor);
        } else if (binradar_query_window_file != NULL) {
            log_msg("[snapshot] [query-window] [skip] [query-cursor %lld] "
                    "[expr-cursor %lld]\n", (long long)query_cursor,
                    (long long)expr_cursor);
        }
    }
}

static void snapshot_modification_manager_free(ModificationManager *manager)
{
    if (manager == NULL) {
        return;
    }
    if (manager->modifications != NULL) {
        g_queue_free_full(manager->modifications,
                          (GDestroyNotify)snapshot_mutation_free);
    }
    snapshot_mutation_free(manager->current);
    g_free(manager);
}

static void snapshot_mutation_history_free(void)
{
    GHashTable *value_tables[] = {
        g_read_access_tainted_primitives_all,
        g_read_access_pointers_all,
    };
    GHashTable *alias_tables[] = {
        g_read_access_tainted_primitives_original,
        g_read_access_pointers_original,
    };
    for (size_t ti = 0; ti < G_N_ELEMENTS(value_tables); ti++) {
        GHashTable *table = value_tables[ti];
        if (table != NULL) {
            GHashTableIter iter;
            gpointer key, value;
            g_hash_table_iter_init(&iter, table);
            while (g_hash_table_iter_next(&iter, &key, &value)) {
                g_free(value);
            }
            g_hash_table_destroy(table);
        }
        if (ti == 0) g_read_access_tainted_primitives_all = NULL;
        if (ti == 1) g_read_access_pointers_all = NULL;
    }
    if (alias_tables[0] != NULL) {
        g_hash_table_destroy(alias_tables[0]);
        g_read_access_tainted_primitives_original = NULL;
    }
    if (alias_tables[1] != NULL) {
        g_hash_table_destroy(alias_tables[1]);
        g_read_access_pointers_original = NULL;
    }
}

static void snapshot_modification_manager_reset(bool analysis_started)
{
    snapshot_modification_manager_free(mod_manager);
    mod_manager = NULL;
    snapshot_mutation_baseline_free(snapshot_mutation_baseline);
    snapshot_mutation_baseline = NULL;
    snapshot_mutation_history_free();
    mutation_analysis_started = analysis_started;
}


bool snapshot_mutation_writable_span(target_ulong addr,
                                     uint32_t size)
{
    uint64_t end;
    target_ulong page;

    if (addr < SNAPSHOT_PAGE_SIZE || size == 0 ||
        (uint64_t)addr > UINT64_MAX - size) return false;
    end = (uint64_t)addr + size;
    if (end <= (uint64_t)addr) return false;
    page = addr & SNAPSHOT_PAGE_MASK;
    for (;;) {
        if (!is_valid_address(page, true)) return false;
        if ((uint64_t)page + SNAPSHOT_PAGE_SIZE >= end) break;
        if (page > UINT64_MAX - SNAPSHOT_PAGE_SIZE) return false;
        page += SNAPSHOT_PAGE_SIZE;
    }
    return true;
}

typedef struct SnapshotMutationChildWrite {
    SnapshotMutationWrite local;
    target_ulong before_value;
    target_ulong fresh_target;
} SnapshotMutationChildWrite;

/* Called after fork to keep clean initial state.  All destination and target
 * checks happen before a register or cell is published.  Fresh mappings may
 * exist in a child that is about to terminate, but no partially applied plan
 * can resume guest execution. */
static void snapshot_modify_memory(CPUArchState *cpu_env)
{
    SnapshotMutationPlan *plan;
    SnapshotMutationChildWrite *writes;

    if (mod_manager == NULL) {
        /* Initial run: no modification. */
        return;
    }
    plan = mod_manager->current;
    if (plan == NULL || plan->mods == NULL || plan->num_mods == 0) {
        log_msg("ERROR: empty mutation plan\n");
        exit_with_status(1);
    }
    writes = g_try_malloc0((size_t)plan->num_mods * sizeof(*writes));
    if (writes == NULL) {
        log_msg("[mod] [apply-error] child write staging allocation failed\n");
        exit_with_status(1);
    }

    /* Phase 1: validate every write and the complete destination tuple. */
    for (uint32_t i = 0; i < plan->num_mods; i++) {
        const SnapshotMutationWrite *write = &plan->mods[i];
        SnapshotMutationChildWrite *prepared = &writes[i];
        if (write->kind != SNAPSHOT_MUTATION_BYTES &&
            write->kind != SNAPSHOT_MUTATION_POINTER_NULL &&
            write->kind != SNAPSHOT_MUTATION_POINTER_OOB &&
            write->kind != SNAPSHOT_MUTATION_POINTER_FRESH) {
            log_msg("[mod] [apply-error] invalid mutation kind\n");
            g_free(writes);
            exit_with_status(1);
        }
        if (write->size == 0 || write->size > sizeof(write->value) ||
            (write->kind != SNAPSHOT_MUTATION_BYTES &&
             write->size != sizeof(target_ulong))) {
            log_msg("[mod] [apply-error] invalid mutation width\n");
            g_free(writes);
            exit_with_status(1);
        }
        if (write->kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
            if (write->target.extent == 0 ||
                write->target.extent > SNAPSHOT_PAGE_SIZE ||
                write->target.bytes == NULL) {
                log_msg("[mod] [apply-error] invalid fresh target\n");
                g_free(writes);
                exit_with_status(1);
            }
        } else if (write->target.extent != 0 ||
                   write->target.bytes != NULL) {
            log_msg("[mod] [apply-error] inactive target is populated\n");
            g_free(writes);
            exit_with_status(1);
        }
        if (write->addr < SNAPSHOT_PAGE_SIZE) {
            if (write->addr >= CPU_NB_REGS) {
                log_msg("[mod] [apply-error] invalid mutation register\n");
                g_free(writes);
                exit_with_status(1);
            }
            for (uint32_t prior = 0; prior < i; prior++) {
                if (writes[prior].local.addr == write->addr &&
                    writes[prior].local.addr < SNAPSHOT_PAGE_SIZE) {
                    log_msg("[mod] [apply-error] duplicate register\n");
                    g_free(writes);
                    exit_with_status(1);
                }
            }
        } else if (!snapshot_mutation_writable_span(write->addr,
                                                    write->size)) {
            log_msg("[mod] [apply-error] unwritable destination\n");
            g_free(writes);
            exit_with_status(1);
        }
        for (uint32_t prior = 0; prior < i; prior++) {
            const SnapshotMutationWrite *previous = &writes[prior].local;
            uint64_t previous_end;
            uint64_t current_end;
            if (previous->addr < SNAPSHOT_PAGE_SIZE ||
                write->addr < SNAPSHOT_PAGE_SIZE) continue;
            previous_end = (uint64_t)previous->addr + previous->size;
            current_end = (uint64_t)write->addr + write->size;
            if ((uint64_t)write->addr < previous_end &&
                (uint64_t)previous->addr < current_end) {
                log_msg("[mod] [apply-error] overlapping destinations\n");
                g_free(writes);
                exit_with_status(1);
            }
        }
        prepared->local = *write;
        if (write->addr < SNAPSHOT_PAGE_SIZE) {
            prepared->before_value = cpu_env->regs[(size_t)write->addr];
        } else {
            memcpy(&prepared->before_value, g2h(write->addr), write->size);
        }
    }

    /* Phase 2: allocate and initialize every fresh target while all cells
     * still have their baseline values. */
    for (uint32_t i = 0; i < plan->num_mods; i++) {
        SnapshotMutationChildWrite *prepared = &writes[i];
        if (prepared->local.kind != SNAPSHOT_MUTATION_POINTER_FRESH) continue;
        prepared->fresh_target = snapshot_alloc_pointer_target(
            cpu_env, prepared->local.target.extent);
        if (prepared->fresh_target == (target_ulong)-1 ||
            !snapshot_apply_fresh_target(
                cpu_env, prepared->fresh_target,
                prepared->local.target.bytes,
                prepared->local.target.extent)) {
            snapshot_test_observe_write(&prepared->local, 0,
                                        prepared->before_value, false);
            log_msg("[mod-pointer] [apply-error] fresh target failed\n");
            g_free(writes);
            exit_with_status(1);
        }
        memcpy(prepared->local.value, &prepared->fresh_target,
               sizeof(prepared->fresh_target));
    }

    /* Phase 3: publish the complete tuple in canonical plan order. */
    for (uint32_t i = 0; i < plan->num_mods; i++) {
        SnapshotMutationChildWrite *prepared = &writes[i];
        SnapshotMutationWrite *write = &prepared->local;
        if (write->addr < SNAPSHOT_PAGE_SIZE) {
            target_ulong reg_value = 0;
            memcpy(&reg_value, write->value, sizeof(reg_value));
            cpu_env->regs[(size_t)write->addr] = reg_value;
            sem_reg_overwrite(cpu_env, (int)write->addr, SEM_OP_SNAPSHOT);
            log_msg("[mod-reg] [register %ld] [size %ld] [total %d]\n",
                    write->addr, write->size,
                    g_queue_get_length(mod_manager->modifications));
        } else {
            memcpy(g2h(write->addr), write->value, write->size);
            sem_mem_overwrite(cpu_env, write->addr, write->size,
                              SEM_OP_SNAPSHOT);
            log_msg("[mod] [addr %lx] [size %ld] [total %d]\n",
                    write->addr, write->size,
                    g_queue_get_length(mod_manager->modifications));
        }
        snapshot_test_observe_write(write, prepared->fresh_target,
                                    prepared->before_value, true);
    }
    g_free(writes);
}

#ifdef SNAPSHOT_DEBUG
static void snapshot_sig_handler(int sig, siginfo_t *si, void *ctx) {
    CPUState *cpu = thread_cpu;
    CPUArchState *env = cpu ? cpu->env_ptr : NULL;
    snapshot_record_guest_crash(env, 0, sig, si ? si->si_code : 0, 0, si ? (uintptr_t)si->si_addr : 0, "host crashed!!");
    void *frames[SNAPSHOT_BT_DEPTH];
    int n = backtrace(frames, SNAPSHOT_BT_DEPTH);
    dprintf(STDERR_FILENO, "[forkserver-child] fata signal %d (%s) addr=%p\n", sig, strsignal(sig), si ? si->si_addr : NULL);
    backtrace_symbols_fd(frames, n, STDERR_FILENO);
    exit_with_status(128 + sig);
}

static void snapshot_install_crash_handler(void) {
    struct sigaction sa = {
        .sa_sigaction = snapshot_sig_handler,
        .sa_flags = SA_SIGINFO | SA_RESETHAND
    };
    sigemptyset(&sa.sa_mask);
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);
    sigaction(SIGABRT, &sa, NULL);
}
#endif

static int compare_prim_id_desc(const void *a, const void *b) {
    const PrimitiveAccess *pa = (const PrimitiveAccess *)a;
    const PrimitiveAccess *pb = (const PrimitiveAccess *)b;
    
    if (pa->access_id > pb->access_id) return -1;
    if (pa->access_id < pb->access_id) return 1;
    return 0;
}

static int compare_ptr_id_desc(const void *a, const void *b) {
    const PointerAccess *pa = (const PointerAccess *)a;
    const PointerAccess *pb = (const PointerAccess *)b;
    
    if (pa->access_id > pb->access_id) return -1;
    if (pa->access_id < pb->access_id) return 1;
    return 0;
}

static void flip_bits(uint8_t *target, int size) {
    for (int i = 0; i < size; i++) {
        target[i] = ~target[i];
    }
}

static void snapshot_mutation_copy_value(uint8_t *dst,
                                          const MutationCandidate *source)
{
    memcpy(dst, source->value,
           sizeof(((SnapshotMutationWrite *)0)->value));
}

/* Generic primitive generation is built completely off-queue.  The source
 * candidate is never modified, and the whole batch becomes visible at once. */
static bool add_modification_primitive(GQueue *modifications,
                                       const MutationCandidate *source)
{
    if (modifications == NULL || source == NULL || source->size == 0 ||
        source->size > sizeof(((SnapshotMutationWrite *)0)->value)) {
        return false;
    }

    uint8_t values[3][sizeof(target_ulong)];
    uint8_t legacy_work[sizeof(target_ulong)];
    memset(values, 0, sizeof(values));
    snapshot_mutation_copy_value(legacy_work, source);
    uint32_t count = 0;
    uint64_t original = 0;
    memcpy(&original, source->value, source->size);

    if (source->size == 1) {
        if (original != 0) {
            legacy_work[0] = 0;
            memcpy(values[count++], legacy_work, sizeof(legacy_work));
        }
        if (original != 1) {
            memcpy(values[count], legacy_work, sizeof(legacy_work));
            values[count++][0] = 1;
        }
        flip_bits(legacy_work, source->size);
        memcpy(values[count++], legacy_work, sizeof(legacy_work));
    } else if (source->size == 2) {
        if (original != 0) {
            snapshot_mutation_copy_value(values[count], source);
            memset(values[count++], 0, source->size);
        }
        if (original != 1) {
            snapshot_mutation_copy_value(values[count], source);
            memset(values[count], 0, source->size);
            values[count++][0] = 1;
            memset(legacy_work, 0, source->size);
            legacy_work[0] = 1;
        }
        flip_bits(legacy_work, source->size);
        memcpy(values[count++], legacy_work, sizeof(legacy_work));
    } else if (source->size == 4 || source->size == 8) {
        if (original != 0) {
            snapshot_mutation_copy_value(values[count], source);
            memset(values[count], 0, source->size);
            count++;
        }
        if (original != 1) {
            snapshot_mutation_copy_value(values[count], source);
            memset(values[count], 0, source->size);
            values[count][0] = 1;
            count++;
        }
        snapshot_mutation_copy_value(values[count], source);
        flip_bits(values[count], source->size);
        count++;
    } else if (source->size < 8) {
        snapshot_mutation_copy_value(values[0], source);
        flip_bits(values[0], source->size);
        count = 1;
    } else {
        /* Preserve the existing no-op policy for unsupported widths. */
        return false;
    }

    SnapshotMutationPlan *batch[3] = {NULL, NULL, NULL};
    for (uint32_t i = 0; i < count; i++) {
        batch[i] = snapshot_mutation_new(source, SNAPSHOT_MUTATION_BYTES,
                                          values[i], source->size, 0, NULL);
        if (batch[i] == NULL) {
            snapshot_mutation_free_batch(batch, count);
            return false;
        }
    }
    return snapshot_mutation_enqueue_batch(modifications, batch, count);
}

static bool add_untyped_pointer_candidate(GQueue *modifications,
                                          const MutationCandidate *source)
{
    uint8_t null_value[sizeof(target_ulong)] = {0};
    SnapshotMutationPlan *mod = snapshot_mutation_new(
        source, SNAPSHOT_MUTATION_POINTER_NULL, null_value, source->size,
        0, NULL);
    if (mod == NULL) {
        return false;
    }
    return snapshot_mutation_enqueue_one(modifications, mod);
}

typedef enum SnapshotPointerSource {
    SNAPSHOT_POINTER_FROM_PRIMITIVE = 0,
    SNAPSHOT_POINTER_FROM_ACCESS = 1,
} SnapshotPointerSource;
/* Resolve one baseline pointer access and enqueue its complete typed batch.
 * This focused Stage 7 source lane uses the same compact resolver as the
 * production coordinator sink below; it does not adapt a decoded full model. */
static bool add_pointer_typed_candidate(
    GQueue *modifications, const MutationCandidate *source,
    const OspreyRuntimeChunkRef *cell,
    const OspreyRuntimeAddressRef *target_ref, bool typed_allowed,
    SnapshotPointerSource source_kind) G_GNUC_UNUSED;

static bool add_pointer_typed_candidate(
    GQueue *modifications, const MutationCandidate *source,
    const OspreyRuntimeChunkRef *cell,
    const OspreyRuntimeAddressRef *target_ref, bool typed_allowed,
    SnapshotPointerSource source_kind)
{
    const OspreyMutationModel *model = NULL;
    OspreyRuntimePointerResolution resolution;
    OspreyRuntimeResolveStatus status;
    uint8_t zero_value[sizeof(target_ulong)] = {0};
    target_ulong concrete_value;
    uint32_t count = 0;
    SnapshotMutationPlan *batch[3] = {NULL, NULL, NULL};

    if (!typed_allowed || source == NULL ||
        source->size != sizeof(target_ulong) || cell == NULL ||
        cell->start.valid != 1 || cell->size != source->size ||
        cell->start.raw != (uint64_t)source->addr || g_osprey_ctx == NULL ||
        !g_osprey_ctx->config.enabled || !osprey_collect_enabled ||
        !osprey_runtime_mutation_prepare(g_osprey_ctx)) {
        goto generic;
    }
    model = osprey_runtime_mutation_model(g_osprey_ctx);
    if (model == NULL) goto generic;
    memcpy(&concrete_value, source->value, sizeof(concrete_value));
    status = osprey_runtime_resolve_pointer(
        g_osprey_ctx, model, cell, concrete_value, target_ref,
        &resolution);
    if (getenv("BINRADAR_OSPREY_TEST_APPLIED_STATE") != NULL) {
        log_msg("[osprey] [test-plan] [addr %lx] [value %lx] [status %d] "
                "[extent %llu] [target-valid %u] [runtime-target %u]\n",
                (unsigned long)source->addr,
                (unsigned long)concrete_value, (int)status,
                (unsigned long long)resolution.target_extent,
                resolution.target_valid, resolution.has_runtime_target);
    }
    if (status != OSPREY_RUNTIME_RESOLVED || resolution.target_extent == 0 ||
        resolution.target_extent > SNAPSHOT_PAGE_SIZE) {
        goto generic;
    }

    if (concrete_value == 0) {
        uint8_t fills[3][SNAPSHOT_PAGE_SIZE];
        memset(fills[0], 0, sizeof(fills[0]));
        memset(fills[1], 1, sizeof(fills[1]));
        memset(fills[2], 0xff, sizeof(fills[2]));
        for (uint32_t i = 0; i < G_N_ELEMENTS(fills); i++) {
            batch[count++] = snapshot_mutation_new(
                source, SNAPSHOT_MUTATION_POINTER_FRESH, zero_value,
                sizeof(target_ulong), resolution.target_extent,
                fills[i]);
            if (batch[count - 1] == NULL) {
                snapshot_mutation_free_batch(batch, count);
                goto generic;
            }
        }
    } else {
        uint64_t target_raw;
        uint64_t target_end;
        uint64_t oob;
        target_ulong oob_value;
        uint8_t oob_bytes[sizeof(target_ulong)];

        if (!resolution.has_runtime_target || !resolution.target_valid ||
            target_ref == NULL) {
            goto generic;
        }
        target_raw = resolution.target.raw;
        if (target_raw > UINT64_MAX - resolution.target_extent) {
            goto generic;
        }
        target_end = target_raw + resolution.target_extent;
        if (target_end <= target_raw || target_end > UINT64_MAX - 0x10u) {
            goto generic;
        }
        oob = target_end + 0x10u;
        if (oob < target_end ||
            (oob >= target_raw && oob < target_end)) {
            goto generic;
        }
        oob_value = (target_ulong)oob;
        if ((uint64_t)oob_value != oob) goto generic;
        memcpy(oob_bytes, &oob_value, sizeof(oob_value));

        batch[count++] = snapshot_mutation_new(
            source, SNAPSHOT_MUTATION_POINTER_NULL, zero_value,
            sizeof(target_ulong), 0, NULL);
        batch[count++] = snapshot_mutation_new(
            source, SNAPSHOT_MUTATION_POINTER_OOB, oob_bytes,
            sizeof(target_ulong), 0, NULL);
        if (batch[0] == NULL || batch[1] == NULL) {
            snapshot_mutation_free_batch(batch, count);
            goto generic;
        }
        batch[0]->mods[0].target.resolved_raw = target_raw;
        batch[0]->mods[0].target.resolved_end = target_end;
        batch[1]->mods[0].target.resolved_raw = target_raw;
        batch[1]->mods[0].target.resolved_end = target_end;
    }
    if (snapshot_mutation_enqueue_batch(modifications, batch, count)) {
        return true;
    }

generic:
    if (source_kind == SNAPSHOT_POINTER_FROM_ACCESS) {
        return add_untyped_pointer_candidate(modifications, source);
    }
    return add_modification_primitive(modifications, source);
}

static bool snapshot_mutation_legacy_emit_family(
    const SnapshotMutationBaselineEntry *entry,
    SnapshotMutationProposalSink *sink)
{
    const OspreyMutationModel *model;
    OspreyRuntimePointerResolution resolution;
    OspreyRuntimeResolveStatus status;
    SnapshotMutationProposalFamily family;
    SnapshotMutationProposalVariant variants[3];
    SnapshotMutationProposalWrite writes[3];
    uint8_t fills[3][SNAPSHOT_PAGE_SIZE];
    target_ulong concrete_value;
    uint32_t count;

    if (entry == NULL || sink == NULL || !entry->typed_eligible ||
        (entry->source_kind != SNAPSHOT_MUTATION_SOURCE_PRIMITIVE &&
         entry->source_kind != SNAPSHOT_MUTATION_SOURCE_POINTER) ||
        entry->size != sizeof(target_ulong) || entry->cell.start.valid != 1 ||
        entry->cell.size != entry->size ||
        entry->cell.start.raw != (uint64_t)entry->addr ||
        g_osprey_ctx == NULL || !g_osprey_ctx->config.enabled ||
        !osprey_collect_enabled ||
        !osprey_runtime_mutation_prepare(g_osprey_ctx)) {
        return false;
    }
    model = osprey_runtime_mutation_model(g_osprey_ctx);
    if (model == NULL) return false;
    memcpy(&concrete_value, entry->planner_bytes, sizeof(concrete_value));
    status = osprey_runtime_resolve_pointer(
        g_osprey_ctx, model, &entry->cell, concrete_value,
        entry->target_ref_valid ? &entry->target_ref : NULL, &resolution);
    if (getenv("BINRADAR_OSPREY_TEST_APPLIED_STATE") != NULL) {
        log_msg("[osprey] [test-plan] [addr %lx] [value %lx] [status %d] "
                "[extent %llu] [target-valid %u] [runtime-target %u]\n",
                (unsigned long)entry->addr, (unsigned long)concrete_value,
                (int)status, (unsigned long long)resolution.target_extent,
                resolution.target_valid, resolution.has_runtime_target);
    }
    if (status != OSPREY_RUNTIME_RESOLVED || resolution.target_extent == 0 ||
        resolution.target_extent > SNAPSHOT_PAGE_SIZE) {
        return false;
    }

    memset(&family, 0, sizeof(family));
    memset(variants, 0, sizeof(variants));
    memset(writes, 0, sizeof(writes));
    family.advisor_id = 1; /* first in-process advisor: OSPREY type */
    family.advisor_priority = 0;
    family.family_id = entry->token.source_ordinal;
    family.primary_seed = entry->token;
    family.seed_semantics = SNAPSHOT_MUTATION_SEED_SNAPSHOT_STATE;
    family.variants = variants;
    memset(fills, 0, sizeof(fills));

    if (concrete_value == 0) {
        memset(fills[1], 1, sizeof(fills[1]));
        memset(fills[2], 0xff, sizeof(fills[2]));
        count = 3;
        for (uint32_t i = 0; i < count; i++) {
            variants[i].variant_id = i;
            variants[i].write_count = 1;
            variants[i].writes = &writes[i];
            writes[i].destination = entry->token;
            writes[i].kind = SNAPSHOT_MUTATION_POINTER_FRESH;
            writes[i].size = sizeof(target_ulong);
            writes[i].target_extent = resolution.target_extent;
            writes[i].target_bytes = fills[i];
            memcpy(writes[i].value, entry->planner_bytes,
                   sizeof(writes[i].value));
        }
    } else {
        uint64_t target_raw;
        uint64_t target_end;
        uint64_t oob;
        target_ulong oob_value;

        if (!resolution.has_runtime_target || !resolution.target_valid ||
            !entry->target_ref_valid) {
            return false;
        }
        target_raw = resolution.target.raw;
        if (target_raw > UINT64_MAX - resolution.target_extent) return false;
        target_end = target_raw + resolution.target_extent;
        if (target_end <= target_raw || target_end > UINT64_MAX - 0x10u) {
            return false;
        }
        oob = target_end + 0x10u;
        if (oob < target_end ||
            (oob >= target_raw && oob < target_end)) return false;
        oob_value = (target_ulong)oob;
        if ((uint64_t)oob_value != oob) return false;
        count = 2;
        for (uint32_t i = 0; i < count; i++) {
            variants[i].variant_id = i;
            variants[i].write_count = 1;
            variants[i].writes = &writes[i];
            writes[i].destination = entry->token;
            writes[i].size = sizeof(target_ulong);
            writes[i].target_extent = 0;
            writes[i].target_bytes = NULL;
            writes[i].resolved_raw = target_raw;
            writes[i].resolved_end = target_end;
        }
        writes[0].kind = SNAPSHOT_MUTATION_POINTER_NULL;
        writes[1].kind = SNAPSHOT_MUTATION_POINTER_OOB;
        memcpy(writes[1].value, &oob_value, sizeof(oob_value));
    }
    family.variant_count = count;
    return snapshot_mutation_sink_submit(sink, &family);
}

static void snapshot_mutation_legacy_advisor(
    const SnapshotMutationBaseline *baseline,
    SnapshotMutationProposalSink *sink)
{
    if (baseline == NULL || sink == NULL) return;
    for (uint32_t i = 0; i < baseline->entry_count; i++) {
        (void)snapshot_mutation_legacy_emit_family(&baseline->entries[i], sink);
    }
}

// In parent process, called after child execution
// Return: remaining modifications
static int select_next_modification(SnapshotExitInfo *exit_info) {
    (void)exit_info;

    if (mod_manager == NULL) {
        return 0;
    }

    if (mod_manager->current != NULL) {
        snapshot_mutation_free(mod_manager->current);
        mod_manager->current = NULL;
    }
    mod_manager->current = g_queue_pop_head(mod_manager->modifications);
    if (mod_manager->current == NULL) {
        log_msg("[analyze] [done] consumed all modifications\n");
        if (shared_trace_data != NULL) {
            memset(shared_trace_data, 0, sizeof(SharedTraceData));
        }
        snapshot_modification_manager_reset(true);
        return 0;
    }

    // Finished: reset shared_trace_data
    memset(shared_trace_data, 0, sizeof(SharedTraceData));
    return g_queue_get_length(mod_manager->modifications) + 1;
}

static bool snapshot_mutation_baseline_add_history(
    uint32_t prim_count, uint32_t ptr_count)
{
    if (g_read_access_tainted_primitives_original == NULL) {
        g_read_access_tainted_primitives_original =
            g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        g_read_access_pointers_original =
            g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        g_read_access_tainted_primitives_all =
            g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
        g_read_access_pointers_all =
            g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, NULL);
    }
    for (uint32_t i = 0; i < prim_count; i++) {
        PrimitiveAccess *copy = g_try_malloc(sizeof(*copy));
        if (copy == NULL) return false;
        *copy = shared_trace_data->primitives[i];
        g_hash_table_insert(g_read_access_tainted_primitives_original,
                            GSIZE_TO_POINTER(copy->addr), copy);
        g_hash_table_insert(g_read_access_tainted_primitives_all,
                            GSIZE_TO_POINTER(copy->addr), copy);
    }
    for (uint32_t i = 0; i < ptr_count; i++) {
        PointerAccess *copy = g_try_malloc(sizeof(*copy));
        if (copy == NULL) return false;
        *copy = shared_trace_data->pointers[i];
        g_hash_table_insert(g_read_access_pointers_original,
                            GSIZE_TO_POINTER(copy->addr), copy);
        g_hash_table_insert(g_read_access_pointers_all,
                            GSIZE_TO_POINTER(copy->addr), copy);
    }
    return true;
}

static void snapshot_mutation_baseline_fill_common(
    SnapshotMutationBaselineEntry *entry, uint64_t epoch,
    uint32_t ordinal, SnapshotMutationLane lane,
    SnapshotMutationSourceKind source_kind, uintptr_t addr, uint32_t size,
    uintptr_t pc, uint64_t access_id, int64_t expr_index,
    int64_t query_index)
{
    memset(entry, 0, sizeof(*entry));
    entry->token.run_epoch = epoch;
    entry->token.source_ordinal = ordinal;
    entry->lane = lane;
    entry->source_kind = source_kind;
    entry->access_id = access_id;
    entry->pc = pc;
    entry->addr = (target_ulong)addr;
    entry->size = size;
    entry->eligible = true;
    entry->typed_eligible = true;
    entry->protected_addr = snapshot_addr_is_protected(entry->addr);
    entry->expr_index = expr_index;
    entry->query_index = query_index;
}

static SnapshotMutationBaseline *snapshot_mutation_baseline_build(
    const SnapshotExitInfo *exit_info, uint32_t prim_count,
    uint32_t ptr_count, bool counts_valid, const ArgumentInfo *arg_info,
    size_t num_arg_regs)
{
    size_t argument_count = 0;
    size_t total;
    uint64_t epoch;
    SnapshotMutationBaseline *baseline;
    uint32_t ordinal = 0;

    if (shared_trace_data == NULL) return NULL;
    for (size_t i = 0; i < num_arg_regs; i++) {
        if (arg_info != NULL && arg_info[i].expr != NULL) argument_count++;
    }
    total = (size_t)prim_count + (size_t)ptr_count + argument_count;
    if (total > UINT32_MAX || total > SIZE_MAX / sizeof(*baseline->entries)) {
        return NULL;
    }
    baseline = snapshot_mutation_try_malloc0(sizeof(*baseline));
    if (baseline == NULL) return NULL;
    epoch = shared_trace_data->run_epoch;
    baseline->run_epoch = epoch;
    baseline->entry_count = (uint32_t)total;
    baseline->counts_valid = counts_valid;
    baseline->query_start = snapshot_mutation_query_start;
    baseline->query_end = (exit_info != NULL)
        ? snapshot_query_cursor_index(exit_info) : -1;
    baseline->expr_start = snapshot_mutation_expr_start;
    baseline->expr_end = (exit_info != NULL)
        ? snapshot_expr_cursor_index(exit_info) : -1;
    /* Half-open [start, end) windows over raw pool differences.  An entry
     * beyond the exit or an unpublished cursor makes the window unusable, so
     * the advisor sees no window rather than a reversed or unbounded one. */
    if (baseline->query_start < 0 || baseline->query_end < 0 ||
        baseline->query_start > baseline->query_end ||
        !snapshot_query_cursor_valid(baseline->query_end)) {
        baseline->query_start = -1;
        baseline->query_end = -1;
    }
    if (baseline->expr_start < 0 || baseline->expr_end < 0 ||
        baseline->expr_start > baseline->expr_end ||
        !snapshot_expr_cursor_valid(baseline->expr_end)) {
        baseline->expr_start = -1;
        baseline->expr_end = -1;
    }
    if (total != 0) {
        baseline->entries = snapshot_mutation_try_malloc0(
            total * sizeof(*baseline->entries));
        if (baseline->entries == NULL) {
            snapshot_mutation_baseline_free(baseline);
            return NULL;
        }
    }

    if (!snapshot_mutation_baseline_add_history(prim_count, ptr_count)) {
        snapshot_mutation_baseline_free(baseline);
        snapshot_mutation_history_free();
        return NULL;
    }

    for (uint32_t i = 0; i < prim_count; i++, ordinal++) {
        const PrimitiveAccess *source = &shared_trace_data->primitives[i];
        SnapshotMutationBaselineEntry *entry = &baseline->entries[ordinal];
        bool epoch_valid = source->run_epoch == epoch;
        snapshot_mutation_baseline_fill_common(
            entry, epoch, ordinal, SNAPSHOT_MUTATION_LANE_PRIMITIVE,
            SNAPSHOT_MUTATION_SOURCE_PRIMITIVE, source->addr,
            source->size > 0 ? (uint32_t)source->size : 0, source->pc,
            source->access_id, source->expr_index, source->query_index);
        if (source->size <= 0 ||
            (uint32_t)source->size > sizeof(entry->planner_bytes)) {
            entry->eligible = false;
            entry->typed_eligible = false;
        } else {
            memcpy(entry->planner_bytes, g2h(source->addr),
                   (size_t)source->size);
        }
        if (epoch_valid && counts_valid) {
            entry->cell = source->cell;
            /* Symbolic metadata is trustworthy only inside the epoch that
             * produced it; the indexes were validated by the finalizer. */
            if (source->observed_read_valid &&
                source->expr_index >= 0 && source->query_index >= 0 &&
                source->expr_index < baseline->expr_end &&
                source->query_index >= baseline->query_start &&
                source->query_index < baseline->query_end &&
                snapshot_expr_cursor_valid(source->expr_index) &&
                snapshot_query_cursor_valid(source->query_index) &&
                source->root_extension <= SNAPSHOT_MUTATION_ROOT_SEXT) {
                memcpy(entry->observed_read_bytes,
                       source->observed_read_bytes,
                       sizeof(entry->observed_read_bytes));
                entry->observed_read_valid = true;
                entry->root_extension =
                    (SnapshotMutationRootExtension)source->root_extension;
            } else {
                entry->observed_read_valid = false;
                entry->expr_index = -1;
                entry->query_index = -1;
            }
        } else {
            memset(&entry->cell, 0, sizeof(entry->cell));
            entry->observed_read_valid = false;
            entry->expr_index = -1;
            entry->query_index = -1;
            entry->typed_eligible = false;
        }
        log_msg("[analyze] [primitive] [index %u] [addr %lx] [size %d] [id %llu]\n",
                i, source->addr, source->size,
                (unsigned long long)source->access_id);
    }
    for (uint32_t i = 0; i < ptr_count; i++, ordinal++) {
        const PointerAccess *source = &shared_trace_data->pointers[i];
        SnapshotMutationBaselineEntry *entry = &baseline->entries[ordinal];
        bool epoch_valid = source->run_epoch == epoch;
        snapshot_mutation_baseline_fill_common(
            entry, epoch, ordinal, SNAPSHOT_MUTATION_LANE_POINTER,
            SNAPSHOT_MUTATION_SOURCE_POINTER, source->addr,
            sizeof(target_ulong), source->pc, source->access_id,
            source->expr_index, source->query_index);
        memcpy(entry->planner_bytes, &source->target,
               sizeof(target_ulong));
        if (epoch_valid && counts_valid) {
            entry->cell = source->cell;
            entry->target_ref = source->target_ref;
            entry->target_ref_valid = source->target != 0 &&
                                      source->target_ref.valid == 1;
            if (source->observed_read_valid &&
                source->expr_index >= 0 && source->query_index >= 0 &&
                source->expr_index < baseline->expr_end &&
                source->query_index >= baseline->query_start &&
                source->query_index < baseline->query_end &&
                snapshot_expr_cursor_valid(source->expr_index) &&
                snapshot_query_cursor_valid(source->query_index) &&
                source->root_extension <= SNAPSHOT_MUTATION_ROOT_SEXT) {
                memcpy(entry->observed_read_bytes,
                       source->observed_read_bytes,
                       sizeof(entry->observed_read_bytes));
                entry->observed_read_valid = true;
                entry->root_extension =
                    (SnapshotMutationRootExtension)source->root_extension;
            } else {
                entry->observed_read_valid = false;
                entry->expr_index = -1;
                entry->query_index = -1;
            }
        } else {
            memset(&entry->cell, 0, sizeof(entry->cell));
            memset(&entry->target_ref, 0, sizeof(entry->target_ref));
            entry->target_ref_valid = false;
            entry->observed_read_valid = false;
            entry->expr_index = -1;
            entry->query_index = -1;
            entry->typed_eligible = false;
        }
        log_msg("[analyze] [pointer] [index %u] [addr %lx] [target %lx] [id %llu]\n",
                i, source->addr, source->target,
                (unsigned long long)source->access_id);
    }
    for (size_t i = 0; i < num_arg_regs; i++) {
        const ArgumentInfo *source = &arg_info[i];
        SnapshotMutationBaselineEntry *entry;
        if (source->expr == NULL) continue;
        entry = &baseline->entries[ordinal];
        bool pointer = is_valid_address(source->value, false);
        snapshot_mutation_baseline_fill_common(
            entry, epoch, ordinal, SNAPSHOT_MUTATION_LANE_ARGUMENT,
            pointer ? SNAPSHOT_MUTATION_SOURCE_ARGUMENT_POINTER
                    : SNAPSHOT_MUTATION_SOURCE_ARGUMENT_PRIMITIVE,
            source->reg, sizeof(target_ulong), 0, i,
            snapshot_expr_index_from_ptr(source->expr), -1);
        memcpy(entry->planner_bytes, &source->value,
               sizeof(target_ulong));
        entry->eligible = !pointer;
        entry->typed_eligible = false;
        entry->protected_addr = snapshot_addr_is_protected(entry->addr);
        log_msg("[analyze] [sym-arg] [%s] [reg %zu] [expr %p]\n",
                pointer ? "ptr" : "prim", i, (void *)source->expr);
        ordinal++;
    }
    return baseline;
}

static void snapshot_mutation_candidate_from_entry(
    const SnapshotMutationBaselineEntry *entry, MutationCandidate *candidate)
{
    memset(candidate, 0, sizeof(*candidate));
    candidate->addr = entry->addr;
    candidate->size = entry->size;
    candidate->kind = entry->source_kind == SNAPSHOT_MUTATION_SOURCE_POINTER
        ? 1 : 0;
    if (entry->expr_index >= 0 && pool != NULL && next_free_expr != NULL) {
        uintptr_t index = (uintptr_t)entry->expr_index;
        uintptr_t count = ((uintptr_t)next_free_expr - (uintptr_t)pool) /
                          sizeof(Expr);
        if (index < count) candidate->expr = pool + index;
    }
    memcpy(candidate->value, entry->planner_bytes,
           sizeof(candidate->value));
}

static gint snapshot_mutation_family_compare(gconstpointer left,
                                             gconstpointer right,
                                             gpointer user_data)
{
    const SnapshotMutationProposalFamily *a =
        *(const SnapshotMutationProposalFamily * const *)left;
    const SnapshotMutationProposalFamily *b =
        *(const SnapshotMutationProposalFamily * const *)right;
    const SnapshotMutationBaseline *baseline = user_data;
    const SnapshotMutationBaselineEntry *ae =
        snapshot_mutation_lookup_entry(baseline, a->primary_seed);
    const SnapshotMutationBaselineEntry *be =
        snapshot_mutation_lookup_entry(baseline, b->primary_seed);
    if (ae != NULL && be != NULL && ae->token.source_ordinal !=
                                      be->token.source_ordinal) {
        return ae->token.source_ordinal < be->token.source_ordinal ? -1 : 1;
    }
    if (a->advisor_priority != b->advisor_priority)
        return a->advisor_priority < b->advisor_priority ? -1 : 1;
    if (a->family_id != b->family_id)
        return a->family_id < b->family_id ? -1 : 1;
    if (a->advisor_id != b->advisor_id)
        return a->advisor_id < b->advisor_id ? -1 : 1;
    return 0;
}

/* Build one owned plan for one complete proposal variant.  Every write in a
 * variant is applied by a single disposable child, so the plan must carry the
 * whole write set atomically: num_mods equals write_count and no partial plan
 * is ever published.  Fresh payloads are deep-copied into plan ownership so
 * the child never reads proponent-owned bytes. */
static SnapshotMutationPlan *snapshot_mutation_new_variant(
    const SnapshotMutationBaseline *baseline,
    const SnapshotMutationProposalVariant *variant)
{
    SnapshotMutationPlan *plan;

    if (baseline == NULL || variant == NULL || variant->writes == NULL ||
        variant->write_count == 0 ||
        variant->write_count > SNAPSHOT_MUTATION_MAX_SPECIALIZED_WRITES) {
        return NULL;
    }
    plan = snapshot_mutation_try_malloc0(sizeof(*plan));
    if (plan == NULL) return NULL;
    plan->num_mods = variant->write_count;
    plan->mods = snapshot_mutation_try_malloc0(
        (size_t)variant->write_count * sizeof(*plan->mods));
    if (plan->mods == NULL) {
        snapshot_mutation_free(plan);
        return NULL;
    }

    for (uint32_t wi = 0; wi < variant->write_count; wi++) {
        const SnapshotMutationProposalWrite *write = &variant->writes[wi];
        const SnapshotMutationBaselineEntry *entry =
            snapshot_mutation_lookup_entry(baseline, write->destination);
        SnapshotMutationWrite *mod = &plan->mods[wi];

        if (entry == NULL || write->size == 0 ||
            write->size > sizeof(mod->value)) {
            snapshot_mutation_free(plan);
            return NULL;
        }
        if (write->kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
            if (write->target_extent == 0 ||
                write->target_extent > SNAPSHOT_PAGE_SIZE ||
                write->target_bytes == NULL ||
                write->target_extent > SIZE_MAX) {
                snapshot_mutation_free(plan);
                return NULL;
            }
            mod->target.bytes = snapshot_mutation_try_malloc(
                (size_t)write->target_extent);
            if (mod->target.bytes == NULL) {
                snapshot_mutation_free(plan);
                return NULL;
            }
            memcpy(mod->target.bytes, write->target_bytes,
                   (size_t)write->target_extent);
        } else if (write->kind != SNAPSHOT_MUTATION_BYTES &&
                   write->kind != SNAPSHOT_MUTATION_POINTER_NULL &&
                   write->kind != SNAPSHOT_MUTATION_POINTER_OOB) {
            snapshot_mutation_free(plan);
            return NULL;
        }
        mod->kind = write->kind;
        mod->addr = entry->addr;
        mod->size = write->size;
        mod->expr_index = entry->expr_index;
        mod->query_index = entry->query_index;
        memcpy(mod->value, write->value, sizeof(mod->value));
        mod->target.extent = write->target_extent;
        mod->target.resolved_raw = write->resolved_raw;
        mod->target.resolved_end = write->resolved_end;
    }
    return plan;
}

static bool snapshot_mutation_stage_family(
    SnapshotMutationCoordinator *coordinator,
    const SnapshotMutationProposalFamily *family)
{
    GPtrArray *local;
    if (coordinator == NULL || family == NULL) return false;
    local = g_ptr_array_new_with_free_func(
        (GDestroyNotify)snapshot_mutation_free);
    if (local == NULL) return false;
    for (uint32_t vi = 0; vi < family->variant_count; vi++) {
        SnapshotMutationPlan *plan = snapshot_mutation_new_variant(
            coordinator->baseline, &family->variants[vi]);
        if (plan == NULL) {
            g_ptr_array_free(local, TRUE);
            return false;
        }
        g_ptr_array_add(local, plan);
    }
    for (guint i = 0; i < local->len; i++) {
        SnapshotMutationPlan *plan = g_ptr_array_index(local, i);
        g_ptr_array_index(local, i) = NULL;
        g_ptr_array_add(coordinator->staged, plan);
    }
    g_ptr_array_set_size(local, 0);
    g_ptr_array_free(local, TRUE);
    return true;
}

static bool snapshot_mutation_stage_generic(
    SnapshotMutationCoordinator *coordinator,
    const SnapshotMutationBaselineEntry *entry)
{
    MutationCandidate candidate;
    GQueue *temporary;
    bool ok;

    if (entry == NULL || !entry->eligible || entry->protected_addr ||
        entry->source_kind == SNAPSHOT_MUTATION_SOURCE_ARGUMENT_POINTER) {
        return true;
    }
    snapshot_mutation_candidate_from_entry(entry, &candidate);
    temporary = g_queue_new();
    if (temporary == NULL) return false;
    if (entry->source_kind == SNAPSHOT_MUTATION_SOURCE_POINTER) {
        ok = add_untyped_pointer_candidate(temporary, &candidate);
    } else {
        ok = add_modification_primitive(temporary, &candidate);
    }
    if (!ok) {
        g_queue_free_full(temporary,
                          (GDestroyNotify)snapshot_mutation_free);
        return false;
    }
    while (!g_queue_is_empty(temporary)) {
        SnapshotMutationPlan *plan = g_queue_pop_head(temporary);
        g_ptr_array_add(coordinator->staged, plan);
    }
    g_queue_free(temporary);
    return true;
}

static bool snapshot_mutation_coordinator_publish(
    SnapshotMutationCoordinator *coordinator, GQueue *queue)
{
    if (coordinator == NULL || coordinator->baseline == NULL ||
        coordinator->staged == NULL || queue == NULL) return false;
    if (coordinator->staged->len == 0) return true;
    SnapshotMutationPlan **plans = (SnapshotMutationPlan **)
        coordinator->staged->pdata;
    size_t count = coordinator->staged->len;
    bool ok = snapshot_mutation_enqueue_plan_array(queue, plans, count);
    g_ptr_array_set_size(coordinator->staged, 0);
    return ok;
}

static bool snapshot_mutation_coordinator_build(
    SnapshotMutationBaseline *baseline, GQueue *queue)
{
    SnapshotMutationCoordinator coordinator;
    SnapshotMutationProposalSink sink;
    bool *specialized;

    if (baseline == NULL || queue == NULL) return false;
    memset(&coordinator, 0, sizeof(coordinator));
    coordinator.baseline = baseline;
    coordinator.families = g_ptr_array_new_with_free_func(
        snapshot_mutation_proposal_family_free);
    coordinator.staged = g_ptr_array_new_with_free_func(
        (GDestroyNotify)snapshot_mutation_free);
    if (coordinator.families == NULL || coordinator.staged == NULL) {
        snapshot_mutation_coordinator_clear(&coordinator);
        return false;
    }
    sink.coordinator = &coordinator;
    sink.advisor_id = 1;
    sink.advisor_priority = 0;
    if (g_osprey_ctx != NULL && g_osprey_ctx->config.analysis_mode ==
            OSPREY_ANALYSIS_MODE_MUTATION) {
        (void)osprey_runtime_mutation_prepare(g_osprey_ctx);
    }
    snapshot_mutation_legacy_advisor(baseline, &sink);

    /* Symbolic boundary advice runs after compact OSPREY preparation and
     * before family sorting.  Capacity is decided by the per-advisor quotas,
     * not by invocation order, so a disabled advisor cannot change OSPREY's
     * accepted set. */
    if (snapshot_symbolic_mode() != SNAPSHOT_SYMBOLIC_OFF) {
        SnapshotSymbolicView view;
        SnapshotMutationProposalSink symbolic_sink;

        memset(&view, 0, sizeof(view));
        view.expr_base = pool;
        view.query_base = query_queue;
        view.expr_entry = baseline->expr_start;
        view.expr_exit = baseline->expr_end;
        view.query_entry = baseline->query_start;
        view.query_exit = baseline->query_end;
        view.baseline = baseline;
        view.run_epoch = baseline->run_epoch;
        symbolic_sink.coordinator = &coordinator;
        symbolic_sink.advisor_id = SNAPSHOT_SYMBOLIC_ADVISOR_ID;
        symbolic_sink.advisor_priority = SNAPSHOT_SYMBOLIC_ADVISOR_PRIORITY;
        if (view.expr_entry < 0 || view.expr_exit < 0 ||
            view.query_entry < 0 || view.query_exit < 0) {
            log_msg("[symbolic-advisor] [summary] [mode skip] "
                    "[reason invalid-window]\n");
        } else {
            (void)snapshot_symbolic_run(
                &view,
                snapshot_symbolic_mode() == SNAPSHOT_SYMBOLIC_BOUNDARY
                    ? &symbolic_sink : NULL);
        }
    }

    g_ptr_array_sort_with_data(coordinator.families,
                               snapshot_mutation_family_compare, baseline);
    specialized = g_try_malloc0((size_t)baseline->entry_count *
                                sizeof(*specialized));
    if (specialized == NULL && baseline->entry_count != 0) {
        snapshot_mutation_coordinator_clear(&coordinator);
        return false;
    }
    for (guint fi = 0; fi < coordinator.families->len; fi++) {
        SnapshotMutationProposalFamily *family =
            g_ptr_array_index(coordinator.families, fi);
        const SnapshotMutationBaselineEntry *primary =
            snapshot_mutation_lookup_entry(baseline, family->primary_seed);
        bool staged = snapshot_mutation_stage_family(&coordinator, family);
        if (staged && primary != NULL) {
            specialized[primary->token.source_ordinal] = true;
        }
    }
    for (uint32_t i = 0; i < baseline->entry_count; i++) {
        if (!specialized[i] &&
            !snapshot_mutation_stage_generic(&coordinator,
                                             &baseline->entries[i])) {
            g_free(specialized);
            snapshot_mutation_coordinator_clear(&coordinator);
            return false;
        }
    }
    g_free(specialized);
    bool published = snapshot_mutation_coordinator_publish(&coordinator,
                                                            queue);
    snapshot_mutation_coordinator_clear(&coordinator);
    return published;
}

static int analyze_collected_data(const ArgumentInfo *arg_info, size_t num_arg_regs) {
    if (shared_trace_data == NULL) {
        log_msg("Snapshot init error: shared_trace_data is null\n");
        exit_with_status(1);
    }
    // Analyze exit reason
    SnapshotExitInfo *exit_info = snapshot_exit_info_ptr();
    if (!exit_info || !exit_info->valid) {
        log_msg("[analyze] [exit-error] no exit info!!!\n");
        return 0;
    }
    bool is_crash = exit_info->crashed;
    if (is_crash) {
        const char *host_name =
                    (exit_info->host_signal > 0) ? strsignal(exit_info->host_signal) : NULL;
        if (exit_info->target_signal == 0) {
            log_msg("[analyze] [host-crash] [exit %d] [addr %lx] [reason %s] [name %s] [last %lx] Host crashed!!!\n", exit_info->host_signal, exit_info->host_fault_addr, exit_info->description, host_name ? host_name : "unknown", exit_info->guest_last_translation_block);
            exit_with_status(1);
        }
        log_msg("[analyze] [crash] [exit %d] [target %d] [host %d] [name %s] [fault-addr %lx] [guest-pc %lx] [guest-cs %lx] [si-code %d] [last %lx]\n", exit_info->exit_code, exit_info->target_signal, exit_info->host_signal, host_name ? host_name : "unknown", exit_info->fault_addr, exit_info->guest_pc, exit_info->guest_cs_base, exit_info->si_code, exit_info->guest_last_translation_block);
    } else {
        log_msg("[analyze] [normal] [exit %d] [guest-pc %lx] [guest-cs %lx] [reason %s] [last %lx]\n", exit_info->exit_code, exit_info->guest_pc, exit_info->guest_cs_base, exit_info->description, exit_info->guest_last_translation_block);
    }

    // Analyze shared_trace_data
    /* Stage 7.1: bound the parent's consumption.  prim_idx/ptr_idx are
     * child-written counters that normally stay at or below the record
     * capacity (LRU replacement), but a defensive-path increment or an
     * inconsistent removal can push them past it; consuming an
     * out-of-range count would sort and read past the fixed record
     * arrays.  Snapshot the counts once, clamp, and disable typed
     * consumption when the counts or the sticky overflow flags say the
     * record set is not trustworthy. */
    uint32_t raw_prim_count = shared_trace_data->prim_idx;
    uint32_t raw_ptr_count = shared_trace_data->ptr_idx;
    bool prim_count_valid = raw_prim_count <= MAX_PRIMITIVE_ACCESS;
    bool ptr_count_valid = raw_ptr_count <= MAX_POINTER_ACCESS;
    bool counts_valid =
        shared_trace_data->prim_overflow == 0 &&
        shared_trace_data->ptr_overflow == 0 &&
        prim_count_valid && ptr_count_valid;
    /* An over-cap count does not identify a safe initialized prefix: do
     * not sort or traverse that array.  A sticky writer flag with an
     * in-range count retains the known bounded prefix for the generic
     * path, while typed lookup remains disabled for the baseline. */
    uint32_t prim_count = prim_count_valid ? raw_prim_count : 0;
    uint32_t ptr_count = ptr_count_valid ? raw_ptr_count : 0;
    if (!counts_valid) {
        log_msg("[analyze] [count-clamp] [prim %u->%u] [ptr %u->%u] [prim-ovf %u] [ptr-ovf %u] typed-unavailable\n",
                raw_prim_count, prim_count, raw_ptr_count, ptr_count,
                shared_trace_data->prim_overflow,
                shared_trace_data->ptr_overflow);
    }
    // Sort by access_id
    qsort(shared_trace_data->primitives, prim_count, sizeof(PrimitiveAccess), compare_prim_id_desc);
    qsort(shared_trace_data->pointers, ptr_count, sizeof(PointerAccess), compare_ptr_id_desc);
    /* First run: freeze the validated baseline and publish one complete
     * coordinator plan.  Later iterations only retire the current plan. */
    if (!mutation_analysis_started) {
        SnapshotMutationBaseline *baseline;
        mod_manager_init(exit_info);
        memcpy(&original_exit_info, exit_info, sizeof(SnapshotExitInfo));

        baseline = snapshot_mutation_baseline_build(
            exit_info, prim_count, ptr_count, counts_valid, arg_info,
            num_arg_regs);
        if (baseline == NULL) {
            log_msg("[analyze] [mutation-error] baseline allocation failed\n");
            exit_with_status(1);
        }
        snapshot_mutation_baseline_free(snapshot_mutation_baseline);
        snapshot_mutation_baseline = baseline;
        if (!snapshot_mutation_coordinator_build(
                snapshot_mutation_baseline, mod_manager->modifications)) {
            log_msg("[analyze] [mutation-error] coordinator publication failed\n");
            exit_with_status(1);
        }
        log_msg("[analyze] [baseline] [epoch %llu] [entries %u] "
                "[counts-valid %s] [query-end %lld] [expr-end %lld]\n",
                (unsigned long long)baseline->run_epoch,
                baseline->entry_count, baseline->counts_valid ? "true" : "false",
                (long long)baseline->query_end,
                (long long)baseline->expr_end);
        log_msg("[analyze] [queue] [len %d]\n",
                g_queue_get_length(mod_manager->modifications));
        return select_next_modification(exit_info);
    }
    return select_next_modification(exit_info);
}

static int binradar_manager_cur_patch_id(BinradarManager *manager, int new_patch_id) {
    if (manager == NULL) return -1;
    if (manager->current == NULL) return -1;
    if (new_patch_id >= 0) {
        *manager->cur_patch_id = new_patch_id;
    }
    return *manager->cur_patch_id;
}

static int binradar_manager_cur_iter(BinradarManager *manager, int new_iter) {
    if (manager == NULL) return -1;
    if (manager->current == NULL) return -1;
    if (new_iter >= 0) {
        *manager->cur_iter = new_iter;
    }
    return *manager->cur_iter;
}

// Actual patch id for iteration index (0 = original program, then candidates)
static int binradar_manager_patch_id_at(BinradarManager *manager, uint32_t index) {
    if (manager == NULL) return 0;
    if (index == 0) return 0;
    if (index > manager->patch_cnt) return 0;
    if (manager->patch_list == NULL) return (int)index;
    return (int)manager->patch_list[index - 1];
}

static int64_t binradar_shift_right(int64_t value, int64_t amount)
{
    if (amount >= 64) return value < 0 ? -1 : 0;
    if (amount <= -64) return 0;
    if (amount < 0) return (int64_t)((uint64_t)value << (uint64_t)-amount);
    if (amount == 0) return value;
    uint64_t bits = (uint64_t)value >> (uint64_t)amount;
    if (value < 0) bits |= ~(uint64_t)0 << (64u - (uint64_t)amount);
    return (int64_t)bits;
}

static int64_t binradar_shift_left(int64_t value, int64_t amount)
{
    if (amount >= 64) return 0;
    if (amount <= -64) return value < 0 ? -1 : 0;
    if (amount < 0) return binradar_shift_right(value, -amount);
    return (int64_t)((uint64_t)value << (uint64_t)amount);
}

static bool binradar_eval_expr(const BinradarCachePredicate *predicate,
                               uint32_t index, const uint64_t regs[16],
                               int64_t *value, bool *crashed)
{
    if (predicate->expr_nodes == NULL ||
        index >= predicate->expr_nodes->len) return false;
    const BinradarExprNode *node = &g_array_index(
        predicate->expr_nodes, BinradarExprNode, index);
    int64_t left = 0, right = 0;
    if (node->op == BRCACHE_EXPR_LITERAL) {
        *value = node->literal;
        return true;
    }
    if (node->op == BRCACHE_EXPR_VARIABLE) {
        *value = (int64_t)regs[node->variable];
        return true;
    }
    if (!binradar_eval_expr(predicate, node->left, regs, &left, crashed)) {
        return false;
    }
    if (node->op == BRCACHE_EXPR_NOT) {
        *value = ~left;
        return true;
    }
    if (!binradar_eval_expr(predicate, node->right, regs, &right, crashed)) {
        return false;
    }
    switch (node->op) {
    case BRCACHE_EXPR_EQ: *value = left == right; break;
    case BRCACHE_EXPR_NE: *value = left != right; break;
    case BRCACHE_EXPR_GT: *value = left > right; break;
    case BRCACHE_EXPR_GE: *value = left >= right; break;
    case BRCACHE_EXPR_LT: *value = left < right; break;
    case BRCACHE_EXPR_LE: *value = left <= right; break;
    case BRCACHE_EXPR_ADD:
        *value = (int64_t)((uint64_t)left + (uint64_t)right); break;
    case BRCACHE_EXPR_SUB:
        *value = (int64_t)((uint64_t)left - (uint64_t)right); break;
    case BRCACHE_EXPR_MUL:
        *value = (int64_t)((uint64_t)left * (uint64_t)right); break;
    case BRCACHE_EXPR_DIV:
        if (right == 0 || (left == INT64_MIN && right == -1)) {
            *crashed = true;
            *value = 0;
        } else {
            *value = left / right;
        }
        break;
    case BRCACHE_EXPR_REM:
        if (right == 0 || (left == INT64_MIN && right == -1)) {
            *crashed = true;
            *value = 0;
        } else {
            *value = left % right;
        }
        break;
    case BRCACHE_EXPR_AND: *value = left & right; break;
    case BRCACHE_EXPR_OR: *value = left | right; break;
    case BRCACHE_EXPR_XOR: *value = left ^ right; break;
    case BRCACHE_EXPR_SHL: *value = binradar_shift_left(left, right); break;
    case BRCACHE_EXPR_SHR: *value = binradar_shift_right(left, right); break;
    default: return false;
    }
    return true;
}

typedef struct BinradarCacheClamp {
    uint64_t begin;
    uint64_t end;
} BinradarCacheClamp;

static bool binradar_cache_read_cell(const BinradarCachePredicate *predicate,
                                     const uint64_t regs[16],
                                     const uint8_t *stack, size_t stack_size,
                                     uint64_t *value)
{
    if (predicate->cell_kind == BRCACHE_CELL_REGISTER) {
        *value = regs[predicate->cell_index];
        return true;
    }
    size_t width = predicate->cell_kind == BRCACHE_CELL_STACK8 ? 1u :
                   predicate->cell_kind == BRCACHE_CELL_STACK16 ? 2u :
                   predicate->cell_kind == BRCACHE_CELL_STACK32 ? 4u : 8u;
    if (predicate->cell_index > SIZE_MAX / width) return false;
    size_t offset = (size_t)predicate->cell_index * width;
    if (offset > stack_size || width > stack_size - offset) return false;
    *value = 0;
    memcpy(value, stack + offset, width);
    return true;
}

static bool binradar_eval_cache_predicate(
        const BinradarManager *manager, uint32_t patch_id,
        const uint64_t regs[16], const BinradarCacheClamp *clamps,
        const uint8_t *stack, size_t stack_size, int *branch)
{
    if (patch_id == 0) {
        *branch = 0;
        return true;
    }
    if (patch_id > manager->cache_predicate_count) return false;
    const BinradarCachePredicate *predicate =
        &manager->cache_predicates[patch_id];
    if (manager->cache_family == BRCACHE_FAMILY_GENERIC) {
        int64_t value = 0;
        bool crashed = false;
        if (!binradar_eval_expr(predicate, predicate->expr_root, regs,
                                &value, &crashed)) return false;
        *branch = crashed ? 2 : value != 0;
        return true;
    }
    uint64_t value;
    if (clamps == NULL ||
        !binradar_cache_read_cell(predicate, regs, stack, stack_size,
                                  &value)) return false;
    if (predicate->cwe_kind == 2) {
        if (value > UINT64_MAX / predicate->scale) {
            *branch = 2;
            return true;
        }
        value *= predicate->scale;
    }
    for (size_t i = 256; i-- > 0;) {
        if (predicate->cwe_kind == 1) {
            if (value >= clamps[i].begin && value < clamps[i].end) {
                *branch = 0;
                return true;
            }
        } else if (value < clamps[i].end - clamps[i].begin) {
            *branch = 0;
            return true;
        }
    }
    *branch = 1;
    return true;
}

static bool binradar_cache_vector(BinradarManager *manager,
                                  uint32_t selected_patch,
                                  uint32_t evaluated_patch,
                                  GArray **vector_out)
{
    GArray *vector = g_array_new(FALSE, FALSE, sizeof(int));
    size_t offset = 0;
    uint64_t expected_flags = manager->cache_family == BRCACHE_FAMILY_CWE805
        ? BRCACHE_FLAG_CWE805 : 0;
    size_t expected_record = sizeof(BinradarSnapshotHeader) +
                             16u * sizeof(uint64_t);
    if (manager->cache_family == BRCACHE_FAMILY_CWE805) {
        expected_record += 256u * sizeof(BinradarCacheClamp) +
                           manager->cache_stack_size;
    }
    while (offset < manager->cache_bytes->len) {
        if (manager->cache_bytes->len - offset <
            sizeof(BinradarSnapshotHeader)) goto invalid;
        BinradarSnapshotHeader header;
        memcpy(&header, manager->cache_bytes->data + offset, sizeof(header));
        if (header.magic != BRCACHE_SNAPSHOT_MAGIC ||
            header.version != BRCACHE_SNAPSHOT_VERSION ||
            header.patch_id != selected_patch || header.branch > 2 ||
            header.flags != expected_flags ||
            header.stack_size !=
                (manager->cache_family == BRCACHE_FAMILY_CWE805
                    ? manager->cache_stack_size : 0) ||
            expected_record > manager->cache_bytes->len - offset) {
            goto invalid;
        }
        const uint8_t *payload = manager->cache_bytes->data + offset +
                                 sizeof(header);
        BinradarCacheClamp clamps_storage[256];
        const BinradarCacheClamp *clamps = NULL;
        if (manager->cache_family == BRCACHE_FAMILY_CWE805) {
            memcpy(clamps_storage, payload, sizeof(clamps_storage));
            clamps = clamps_storage;
            payload += sizeof(clamps_storage);
        }
        uint64_t regs[16];
        memcpy(regs, payload, sizeof(regs));
        payload += sizeof(regs);
        int evaluated;
        if (!binradar_eval_cache_predicate(
                manager, evaluated_patch, regs, clamps, payload,
                manager->cache_family == BRCACHE_FAMILY_CWE805
                    ? manager->cache_stack_size : 0,
                &evaluated)) goto invalid;
        if (evaluated_patch == selected_patch &&
            evaluated != (int)header.branch) goto invalid;
        g_array_append_val(vector, evaluated);
        offset += expected_record;
    }
    *vector_out = vector;
    return true;
invalid:
    g_array_free(vector, TRUE);
    return false;
}

static bool binradar_branch_vectors_equal(const GArray *left,
                                          const GArray *right)
{
    if (left == NULL || right == NULL || left->len != right->len) return false;
    for (guint i = 0; i < left->len; i++) {
        if (g_array_index(left, int, i) != g_array_index(right, int, i)) {
            return false;
        }
    }
    return true;
}

/* A child normally replays from the entry of the function containing
 * PATCH_LOC and reaches the cached dest() action.  A mutation can still divert
 * control before PATCH_LOC; then no text row is written and br_taken remains
 * NULL.  The corresponding capture vector is empty because neither channel
 * observed a patch-site branch.  Keep the committed value NULL -- .brpatched
 * and FINAL encode that honest no-observation state as `[br null]`; publishing
 * an empty array would produce the invalid SBSV token `[br ]`. */
static bool binradar_observed_vector_matches(const GArray *observed,
                                             const GArray *other)
{
    if (observed == NULL) return other != NULL && other->len == 0;
    return binradar_branch_vectors_equal(observed, other);
}

static const char *binradar_feedback_mutation_kind(SnapshotMutationKind kind)
{
    switch (kind) {
    case SNAPSHOT_MUTATION_BYTES: return "bytes";
    case SNAPSHOT_MUTATION_POINTER_NULL: return "pointer-null";
    case SNAPSHOT_MUTATION_POINTER_OOB: return "pointer-oob";
    case SNAPSHOT_MUTATION_POINTER_FRESH: return "pointer-fresh";
    }
    return "invalid";
}

static bool binradar_feedback_write_atomic(const char *path,
                                           const void *data, size_t size)
{
    bool ok = false;
    char *temporary = g_strdup_printf("%s.tmp-%ld", path, (long)getpid());
    int fd = open(temporary, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (fd >= 0) {
        bool complete = write_exact(fd, data, size) == 0 && fsync(fd) == 0;
        int close_status = close(fd);
        fd = -1;
        if (complete && close_status == 0 && rename(temporary, path) == 0) {
            ok = true;
        }
    }
    if (!ok) unlink(temporary);
    g_free(temporary);
    return ok;
}

/* Commit one pair for one real child execution.  Cache-materialized members
 * never call this function: they have no child-local snapshot of their own. */
static bool binradar_feedback_write(BinradarManager *manager,
                                    uint32_t iteration, uint32_t patch_id,
                                    const GArray *branches)
{
    if (manager == NULL || manager->feedback_dir == NULL || iteration <= 1 ||
        manager->cache_bytes == NULL || branches == NULL) return true;
    PatchedResult *run = get_patched_result_tmp(manager, patch_id);
    if (run->patch_id != patch_id || run->representative != patch_id) {
        return false;
    }

    char *stem = g_strdup_printf("iteration-%08u-patch-%08u",
                                 iteration, patch_id);
    char *snapshot_name = g_strconcat(stem, ".brch", NULL);
    char *metadata_name = g_strconcat(stem, ".sbsv", NULL);
    char *snapshot_path = g_build_filename(manager->feedback_dir,
                                           snapshot_name, NULL);
    char *metadata_path = g_build_filename(manager->feedback_dir,
                                           metadata_name, NULL);
    GString *metadata = g_string_new(NULL);
    const bool same_fault = run->is_crash &&
        run->fault_loc == manager->poc_fault_addr;
    const char *result = !run->is_crash ? "benign" :
        same_fault ? "malicious" : "ignored";
    const SnapshotMutationPlan *plan = mod_manager != NULL
        ? mod_manager->current : NULL;
    const uint32_t mutation_writes = plan != NULL ? plan->num_mods : 0;

    GString *branch_text = g_string_new(NULL);
    if (branches->len == 0) {
        g_string_append(branch_text, "none");
    } else {
        for (guint i = 0; i < branches->len; i++) {
            if (i != 0) g_string_append_c(branch_text, ',');
            g_string_append_printf(branch_text, "%d",
                g_array_index(branches, int, i));
        }
    }
    g_string_append_printf(metadata,
        "[binradar-feedback] [version 1] [iteration %u] [patch %u] "
        "[snapshot-file %s] [snapshot-count %u] [branches %s] "
        "[outcome %s] [fault-addr %lx] [poc-fault-addr %lx] "
        "[same-fault %s] [result %s] [mutation-writes %u]\n",
        iteration, patch_id, snapshot_name, branches->len, branch_text->str,
        run->is_crash ? "crash" : "normal", run->fault_loc,
        manager->poc_fault_addr, same_fault ? "true" : "false", result,
        mutation_writes);
    g_string_free(branch_text, TRUE);

    for (uint32_t i = 0; plan != NULL && i < plan->num_mods; i++) {
        const SnapshotMutationWrite *write = &plan->mods[i];
        g_string_append_printf(metadata,
            "[binradar-mutation] [index %u] [kind %s] "
            "[addr %lx] [size %u] [value ", i,
            binradar_feedback_mutation_kind(write->kind), write->addr,
            write->size);
        if (write->kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
            g_string_append(metadata, "dynamic");
        } else {
            for (uint32_t byte = 0; byte < write->size; byte++) {
                g_string_append_printf(metadata, "%02x", write->value[byte]);
            }
        }
        g_string_append_printf(metadata, "] [target-extent %llu]\n",
            (unsigned long long)write->target.extent);
    }

    bool ok = binradar_feedback_write_atomic(
        snapshot_path, manager->cache_bytes->data, manager->cache_bytes->len);
    if (ok) {
        ok = binradar_feedback_write_atomic(metadata_path, metadata->str,
                                            metadata->len);
    }
    if (!ok) {
        unlink(snapshot_path);
        unlink(metadata_path);
        log_msg("[binradar] [feedback] [error write] [iter %u] [patch %u]\n",
                iteration, patch_id);
    } else {
        log_msg("[binradar] [feedback] [commit] [iter %u] [patch %u] "
                "[snapshots %u] [bytes %u] [result %s]\n",
                iteration, patch_id, branches->len, manager->cache_bytes->len,
                result);
    }
    g_string_free(metadata, TRUE);
    g_free(metadata_path);
    g_free(snapshot_path);
    g_free(metadata_name);
    g_free(snapshot_name);
    g_free(stem);
    return ok;
}

static void binradar_cache_disable(BinradarManager *manager,
                                   const char *reason)
{
    if (!manager->cache_inference_enabled) return;
    manager->cache_inference_enabled = false;
    log_msg("[binradar] [cache-disabled] [reason %s]\n", reason);
}

static bool binradar_publish_selector(BinradarManager *manager,
                                      uint32_t patch_id, uint32_t iteration)
{
    if (!manager->cache_enabled) {
        binradar_manager_cur_patch_id(manager, (int)patch_id);
        binradar_manager_cur_iter(manager, (int)iteration);
        return true;
    }
    const char *descriptor = patch_id == 0 ? "p0" :
        manager->cache_predicates[patch_id].descriptor;
    size_t length = descriptor != NULL ? strlen(descriptor) : 0;
    if (length >= manager->selector->descriptor_capacity) return false;

    /* Iteration is the publication flag.  Keep it at the unpublished value
     * until the complete descriptor and patch id are visible. */
    binradar_manager_cur_iter(manager, 0);
    __sync_synchronize();
    memcpy(manager->selector->descriptor, descriptor, length + 1u);
    manager->selector->descriptor_length = (uint32_t)length;
    binradar_manager_cur_patch_id(manager, (int)patch_id);
    __sync_synchronize();
    binradar_manager_cur_iter(manager, (int)iteration);
    return true;
}

static void binradar_clear_current(BinradarManager *manager)
{
    if (manager == NULL || manager->current == NULL) return;
    for (uint32_t patch = 0; patch <= manager->patch_max_id; patch++) {
        PatchedResult *result = &manager->current->patch_results[patch];
        if (result->br_taken != NULL) {
            g_array_free(result->br_taken, TRUE);
        }
    }
    memset(manager->current->patch_results, 0,
           sizeof(PatchedResult) * (manager->patch_max_id + 1u));
}

static void binradar_restore_uncached_candidates(BinradarManager *manager,
                                                  bool *uncovered,
                                                  const bool *executed)
{
    if (manager == NULL || uncovered == NULL || executed == NULL) return;
    for (uint32_t i = 0; i < manager->patch_cnt; i++) {
        uint32_t patch = (uint32_t)binradar_manager_patch_id_at(manager,
                                                                i + 1u);
        if (executed[patch]) continue;
        PatchedResult *result = get_patched_result_tmp(manager, patch);
        if (result->br_taken != NULL) {
            g_array_free(result->br_taken, TRUE);
        }
        memset(result, 0, sizeof(*result));
        uncovered[patch] = true;
    }
}

static GArray *binradar_clone_branch_vector(const GArray *source)
{
    GArray *clone = g_array_sized_new(FALSE, FALSE, sizeof(int), source->len);
    if (source->len != 0) {
        g_array_append_vals(clone, source->data, source->len);
    }
    return clone;
}

static void binradar_record_outcome(BinradarManager *manager,
                                    uint32_t patch_id)
{
    SnapshotExitInfo *info = snapshot_exit_info_ptr();
    PatchedResult *result = get_patched_result_tmp(manager, patch_id);
    if (info == NULL || !info->valid) return;
    result->patch_id = patch_id;
    result->representative = patch_id;
    result->is_crash = info->crashed;
    result->fault_loc = info->fault_addr;
}

static void binradar_materialize_cache_hit(BinradarManager *manager,
                                           uint32_t patch_id,
                                           uint32_t representative,
                                           const GArray *branches)
{
    SnapshotExitInfo *info = snapshot_exit_info_ptr();
    PatchedResult *result = get_patched_result_tmp(manager, patch_id);
    result->patch_id = patch_id;
    result->representative = representative;
    result->br_taken = branches->len == 0
        ? NULL : binradar_clone_branch_vector(branches);
    if (info != NULL && info->valid) {
        result->is_crash = info->crashed;
        result->fault_loc = info->fault_addr;
    }
}

static gint binradar_compare_u32(gconstpointer left, gconstpointer right)
{
    uint32_t a = *(const uint32_t *)left;
    uint32_t b = *(const uint32_t *)right;
    return a < b ? -1 : a > b;
}

static void binradar_commit(BinradarManager *manager)
{
    if (manager == NULL || manager->current == NULL ||
        manager->evidence_file == NULL) return;
    int cur_iter = binradar_manager_cur_iter(manager, -1);
    if (cur_iter < 1) return;

    GArray **members = g_new0(GArray *, manager->patch_max_id + 1u);
    uint32_t result_count = cur_iter == 1 ? 1u : manager->patch_cnt + 1u;
    uint32_t group_count = 0;
    for (uint32_t i = 0; i < result_count; i++) {
        uint32_t patch = (uint32_t)binradar_manager_patch_id_at(manager, i);
        PatchedResult *result = &manager->current->patch_results[patch];
        uint32_t representative = result->representative;
        if (result->patch_id != patch || representative > manager->patch_max_id) {
            log_msg("[binradar] [evidence] [error incomplete-result] "
                    "[iter %d] [patch %u]\n", cur_iter, patch);
            exit_with_status(1);
        }
        if (members[representative] == NULL) {
            members[representative] = g_array_new(FALSE, FALSE,
                                                   sizeof(uint32_t));
            group_count++;
        }
        g_array_append_val(members[representative], patch);
    }

    GByteArray *payload = g_byte_array_new();
    br_evidence_append_u32(payload, (uint32_t)cur_iter);
    br_evidence_append_u32(payload, group_count);
    for (uint32_t i = 0; i < result_count; i++) {
        uint32_t representative =
            (uint32_t)binradar_manager_patch_id_at(manager, i);
        GArray *group = members[representative];
        if (group == NULL) continue;
        g_array_sort(group, binradar_compare_u32);
        PatchedResult *result =
            &manager->current->patch_results[representative];
        uint8_t outcome = result->is_crash
            ? BR_EVIDENCE_OUTCOME_CRASH : BR_EVIDENCE_OUTCOME_NORMAL;
        uint8_t flags = result->br_taken == NULL
            ? BR_EVIDENCE_GROUP_BRANCH_NULL : 0;
        uint32_t branch_count = result->br_taken != NULL
            ? result->br_taken->len : 0;

        br_evidence_append_u32(payload, representative);
        g_byte_array_append(payload, &outcome, 1);
        g_byte_array_append(payload, &flags, 1);
        br_evidence_append_u16(payload, 0);
        br_evidence_append_u64(payload, result->fault_loc);
        br_evidence_append_u32(payload, branch_count);
        br_evidence_append_u32(payload, group->len);

        uint8_t packed = 0;
        for (uint32_t branch = 0; branch < branch_count; branch++) {
            int value = g_array_index(result->br_taken, int, branch);
            if (value < 0 || value > 2) {
                log_msg("[binradar] [evidence] [error branch] "
                        "[iter %d] [patch %u]\n", cur_iter,
                        representative);
                exit_with_status(1);
            }
            packed |= (uint8_t)value << ((branch % 4u) * 2u);
            if (branch % 4u == 3u || branch + 1u == branch_count) {
                g_byte_array_append(payload, &packed, 1);
                packed = 0;
            }
        }

        uint32_t previous = 0;
        for (guint member_index = 0; member_index < group->len;
             member_index++) {
            uint32_t member = g_array_index(group, uint32_t, member_index);
            uint32_t delta = member_index == 0 ? member : member - previous;
            br_evidence_append_uleb32(payload, delta);
            previous = member;
        }
    }

    if (!br_evidence_write_frame(manager->evidence_file,
                                  BR_EVIDENCE_RECORD_BINRADAR_ITERATION,
                                  payload)) {
        log_msg("[binradar] [evidence] [error write] [iter %d]\n", cur_iter);
        exit_with_status(1);
    }
    log_msg("[binradar] [commit] [iter %d] [groups %u] [patches %u] "
            "[bytes %u]\n", cur_iter, group_count, result_count,
            payload->len);
    g_byte_array_free(payload, TRUE);
    for (uint32_t patch = 0; patch <= manager->patch_max_id; patch++) {
        if (members[patch] != NULL) g_array_free(members[patch], TRUE);
    }
    g_free(members);
    binradar_clear_current(manager);
}

static void set_nonblock(int fd) {
    int flags = fcntl(fd, F_GETFL);
    if (flags < 0) {
        log_msg("fcntl(F_GETFL)");
        exit_with_status(1);
    }
    if (fcntl(fd, F_SETFL, flags | O_NONBLOCK) < 0) {
        log_msg("fcntl(F_SETFL)");
        exit_with_status(1);
    }
}

static PatchedResult *get_patched_result_tmp(BinradarManager *manager, uint32_t patch_id) {
    if (manager == NULL) {
        log_msg("Manager not initialized");
        exit_with_status(1);
    }
    if (manager->current == NULL) {
        log_msg("Current result not initialized");
        exit_with_status(1);
    }
    if (patch_id > manager->patch_max_id) {
        log_msg("Invalid patch ID: %u", patch_id);
        exit_with_status(1);
    }
    return &manager->current->patch_results[patch_id];
}

static void binradar_manager_handle_patch_line(BinradarManager *manager, const char *line) {
    sbsv_row *row = NULL;
    log_msg("[binradar] [patch-res] %s\n", line);
    sbsv_parser_parse_line_detached(manager->patch_result_parser, line, 0, &row);
    int cur_iter = binradar_manager_cur_iter(manager, -1);
    if (row != NULL) {
        if (strcmp(sbsv_row_schema_name(row), "patch") == 0) {
            // Process patch row
            long long patch_id = sbsv_row_get_int(row, "id", NULL);
            long long br = sbsv_row_get_int(row, "br", NULL);
            long long iter = sbsv_row_get_int(row, "v", NULL);
            if (iter != cur_iter) {
                log_msg("[binradar] [iter-mismatch] [v %lld] [iter %d] [id %lld] [br %lld]\n", iter, cur_iter, patch_id, br);
                sbsv_row_free(row);
                return;
            }
            if (patch_id < 0 || patch_id > UINT32_MAX) {
                log_msg("[binradar] [invalid-patch-id] [id %lld]\n", patch_id);
                sbsv_row_free(row);
                return;
            }
            PatchedResult *result = get_patched_result_tmp(manager, patch_id);
            if (result->br_taken == NULL) {
                result->br_taken = g_array_new(FALSE, FALSE, sizeof(int));
            }
            int br_taken = (int)br;
            g_array_append_val(result->br_taken, br_taken);
        }
        sbsv_row_free(row);
    }
}

static void binradar_manager_handle_patch_bytes(BinradarManager *manager, const char *buf, size_t len) {
    for (size_t i = 0; i < len; i++) {
        char c = buf[i];

        if (manager->line_idx + 1 >= sizeof(manager->line_buf)) {
            // Line too long, reset buffer
            manager->line_buf[manager->line_idx] = '\0';
            binradar_manager_handle_patch_line(manager, manager->line_buf);
            manager->line_idx = 0;
        }

        manager->line_buf[manager->line_idx++] = c;

        if (c == '\n') {
            manager->line_buf[manager->line_idx - 1] = '\0';
            binradar_manager_handle_patch_line(manager, manager->line_buf);
            manager->line_idx = 0;
        }
    }
}

static void binradar_manager_drain_patch_fd_once(BinradarManager *manager) {
    char buf[4096];
    for (;;) {
        ssize_t n = read(manager->patch_fd_r, buf, sizeof(buf));
        if (n > 0) {
            binradar_manager_handle_patch_bytes(manager, buf, (size_t)n);
            continue;
        }
        if (n == 0) {
            // write end closed
            break;
        }
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
            break;
        }
        if (errno == EINTR) {
            continue;
        }
        break;
    }
}

static void binradar_manager_drain_cache_fd_once(BinradarManager *manager) {
    uint8_t buf[8192];
    if (manager == NULL || manager->cache_fd_r < 0) return;
    for (;;) {
        ssize_t n = read(manager->cache_fd_r, buf, sizeof(buf));
        if (n > 0) {
            if (!manager->cache_capture_overflow &&
                (size_t)n <= BRCACHE_MAX_CAPTURE_BYTES -
                             manager->cache_bytes->len) {
                g_byte_array_append(manager->cache_bytes, buf, (guint)n);
            } else {
                manager->cache_capture_overflow = true;
            }
            continue;
        }
        if (n == 0 || errno == EAGAIN || errno == EWOULDBLOCK) break;
        if (errno == EINTR) continue;
        manager->cache_capture_overflow = true;
        break;
    }
}

static void binradar_manager_reset_capture(BinradarManager *manager) {
    if (manager == NULL) return;
    manager->line_idx = 0;
    memset(manager->line_buf, 0, sizeof(manager->line_buf));
    if (manager->cache_bytes != NULL) {
        g_byte_array_set_size(manager->cache_bytes, 0);
    }
    manager->cache_capture_overflow = false;
}

static void snapshot_prepare_mutation_epoch(void)
{
    uint64_t epoch;
    if (shared_trace_data == NULL) return;
    /* Half-open raw pool cursors: the baseline child's query suffix and
     * expression arena start here. */
    snapshot_mutation_query_start =
        (query_queue != NULL && next_query != NULL)
            ? (int64_t)(next_query - query_queue) : -1;
    snapshot_mutation_expr_start =
        (pool != NULL && next_free_expr != NULL)
            ? (int64_t)(next_free_expr - pool) : -1;
    epoch = ++next_snapshot_mutation_epoch;
    if (epoch == 0) epoch = ++next_snapshot_mutation_epoch;
    shared_trace_data->run_epoch = epoch;
}

static int64_t forkserver_child_timeout_ms(void) {
    const char *var = getenv("BINRADAR_FORKSERVER_CHILD_TIMEOUT");
    if (var == NULL) return -1;
    int64_t secs = atoll(var);
    if (secs <= 0 || secs > INT64_MAX / 1000) return -1;
    return secs * 1000;
}

static int64_t forkserver_iteration_deadline_us(void) {
    const char *var = getenv("BINRADAR_FORKSERVER_ITERATION_TIMEOUT");
    if (var == NULL) return -1;
    int64_t secs = atoll(var);
    if (secs <= 0 || secs > INT64_MAX / G_USEC_PER_SEC) return -1;
    return g_get_monotonic_time() + secs * G_USEC_PER_SEC;
}

/* Abort an always-hanging mutation plan after this many consecutive
 * child-timeout kills (binradar mode only).  0 disables the abort. */
#define FORKSERVER_ABORT_DEFAULT 10
static int forkserver_timeout_abort_count(void) {
    const char *var = getenv("BINRADAR_FORKSERVER_TIMEOUT_ABORT_COUNT");
    if (var == NULL) return FORKSERVER_ABORT_DEFAULT;
    return atoi(var);
}

/* Parent-side deferred-finding reporter: after the child died (or was
 * killed on timeout), surface any provenance finding the child recorded
 * in shared memory.  Returns true if a finding was reported. */
static bool report_shared_prov_finding(uint32_t *status_out) {
    if (shared_trace_data == NULL) return false;
    /* Acquire-load the shared publication state and copy the whole
     * record once, so a promotion cannot be observed half-written. */
    ProvPublishedFinding fault;
    if (!provenance_snapshot_pending_finding(&fault)) {
        return false;
    }
    ProvFindingRecord *f = &fault.payload;
    /* Emit the structured finding exactly once (dual-record policy). */
    provenance_report_pending_finding();
    /* Synthetic crash verdict (SIGSEGV) so the outer harness sees a crash
     * rather than a pure timeout. */
    if (status_out != NULL) {
        *status_out = 128 + SIGSEGV;
    }
    /* Publish the exit record with the child's final solver cursors
     * (shared pools are attached at the same addresses before fork, so
     * the child's cursor indices are valid in the parent).  The child was
     * killed before guest-exit finalization, so this is the only exit
     * publication for the timeout path. */
    SnapshotExitInfo *info = snapshot_exit_info_ptr();
    if (info != NULL && !info->valid) {
        memset(info, 0, sizeof(*info));
        info->valid = 1;
        info->crashed = 1;
        info->target_signal = TARGET_SIGSEGV;
        info->host_signal = 0;
        info->si_code = SEGV_ACCERR;
        info->exit_code = 139;
        info->guest_pc = f->access_pc;
        info->guest_cs_base = 0;
        info->fault_addr = f->access_pc;
        info->host_fault_addr = 0;
        info->guest_last_translation_block = last_translation_block;
        info->query_cursor = (fault.finding_query_idx >= 0 &&
                              snapshot_query_cursor_valid(
                                  fault.finding_query_idx))
            ? fault.finding_query_idx
            : ((next_query != NULL && query_queue != NULL)
               ? (int64_t)(next_query - query_queue) : -1);
        info->expr_cursor = (fault.finding_expr_idx >= 0 &&
                             snapshot_expr_cursor_valid(
                                 fault.finding_expr_idx))
            ? fault.finding_expr_idx
            : ((next_free_expr != NULL && pool != NULL)
               ? (int64_t)(next_free_expr - pool) : -1);
        const char *pf_reason = provenance_fault_reason();
        g_strlcpy(info->description,
                  pf_reason ? pf_reason : "memcheck: provenance finding",
                  SNAPSHOT_EXIT_DESC_LEN);
        log_msg("[snapshot] [exit] [crash] [entrypoint-hit %lu]\n",
                binradar_entrypoint_hit_count);
        snapshot_log_cursor_indices(info);
        log_msg("[snapshot] [crash] [hit-count %lu] [reason %s] [guest_pc %lx] [guest_cs_base %lx] [fault_addr %lx] [host_fault_addr %lx]\n",
                binradar_entrypoint_hit_count,
                info->description, info->guest_pc, info->guest_cs_base,
                info->fault_addr, info->host_fault_addr);
    }
    return true;
}

/* Wait while draining both result channels.  Return 1 for a child timeout,
 * 2 for the aggregate iteration deadline, and -1 for an internal error. */
static int wait_child_and_drain_patch(pid_t child_pid, uint32_t *status_out,
                                      int64_t iteration_deadline_us) {
    int status = 0;
    int64_t child_timeout_ms = forkserver_child_timeout_ms();
    int64_t child_deadline = child_timeout_ms >= 0
        ? g_get_monotonic_time() + child_timeout_ms * 1000 : -1;
    struct pollfd pfds[2];
    nfds_t nfds = 0;

    if (binradar_manager != NULL) {
        set_nonblock(binradar_manager->patch_fd_r);
        pfds[nfds].fd = binradar_manager->patch_fd_r;
        pfds[nfds].events = POLLIN | POLLHUP | POLLERR;
        nfds++;
        if (binradar_manager->cache_fd_r >= 0) {
            set_nonblock(binradar_manager->cache_fd_r);
            pfds[nfds].fd = binradar_manager->cache_fd_r;
            pfds[nfds].events = POLLIN | POLLHUP | POLLERR;
            nfds++;
        }
    }

    for (;;) {
        pid_t waited = waitpid(child_pid, &status, WNOHANG);
        if (waited == child_pid) break;
        if (waited < 0) {
            log_msg("waitpid(WNOHANG)\n");
            return -1;
        }
        int64_t now = g_get_monotonic_time();
        bool iteration_timeout = iteration_deadline_us >= 0 &&
                                 now >= iteration_deadline_us;
        bool child_timeout = child_deadline >= 0 && now >= child_deadline;
        if (iteration_timeout || child_timeout) {
            log_msg(iteration_timeout
                    ? "[forkserver] [iteration-timeout] killing child %d\n"
                    : "[forkserver] [child-timeout] killing child %d after %ld ms\n",
                    (int)child_pid, (long)child_timeout_ms);
            kill(child_pid, SIGKILL);
            if (waitpid(child_pid, &status, 0) < 0) return -1;
            report_shared_prov_finding((uint32_t *)&status);
            if (binradar_manager != NULL) {
                binradar_manager_drain_patch_fd_once(binradar_manager);
                binradar_manager_drain_cache_fd_once(binradar_manager);
            }
            *status_out = (uint32_t)status;
            return iteration_timeout ? 2 : 1;
        }
        if (nfds == 0) {
            g_usleep(50 * 1000);
            continue;
        }
        int pr = poll(pfds, nfds, 50);
        if (pr < 0) {
            if (errno == EINTR) continue;
            log_msg("poll\n");
            return -1;
        }
        if (pr > 0) {
            if (pfds[0].revents & (POLLIN | POLLHUP | POLLERR)) {
                binradar_manager_drain_patch_fd_once(binradar_manager);
            }
            if (nfds == 2 &&
                (pfds[1].revents & (POLLIN | POLLHUP | POLLERR))) {
                binradar_manager_drain_cache_fd_once(binradar_manager);
            }
        }
    }
    if (binradar_manager != NULL) {
        binradar_manager_drain_patch_fd_once(binradar_manager);
        binradar_manager_drain_cache_fd_once(binradar_manager);
    }
    *status_out = (uint32_t)status;
    return 0;
}


void snapshot_forkserver(CPUState *cpu, CPUArchState *cpu_env,
                         const ArgumentInfo *arg_info, size_t num_arg_regs) {
    log_msg("[snapshot] [forkserver] [called %d]\n", forkserver_installed);
    if (forkserver_installed) return;
    forkserver_installed = true;
    rcu_disable_atfork();
    snapshot_save();
    if (binradar_forkserver_ctrl_r == -1 ||
        binradar_forkserver_stat_w == -1) {
        log_msg("[snapshot] [forkserver] [error] invalid control fds\n");
        exit_with_status(1);
    }

    bool binradar_mode = binradar_manager != NULL;
    uint32_t iteration = 0;
    uint32_t version = BINRADAR_FORKSERVER_PROTOCOL_V3;
    uint32_t expected_reply = version ^ UINT32_MAX;
    uint32_t reply_value;
    int consecutive_child_timeouts = 0;
    int abort_after_timeouts = forkserver_timeout_abort_count();

    if (write_exact(binradar_forkserver_stat_w, &version, sizeof(version)) < 0) {
        exit_with_status(1);
    }
    afl_forksrv_pid = getpid();
    if (read_exact(binradar_forkserver_ctrl_r, &reply_value,
                   sizeof(reply_value)) < 0 ||
        reply_value != expected_reply) {
        log_msg("[snapshot] [forkserver] [error] protocol-v3 handshake\n");
        exit_with_status(1);
    }
    if (write_exact(binradar_forkserver_stat_w, &version, sizeof(version)) < 0) {
        exit_with_status(1);
    }
    log_msg("[forkserver] [start] [protocol 3]\n");

    for (;;) {
        uint32_t was_killed;
        if (read_exact(binradar_forkserver_ctrl_r, &was_killed,
                       sizeof(was_killed)) < 0) {
            log_msg("[forkserver] [exit] parent (fuzzolic) dead or exit\n");
            exit_with_status(2);
        }
        iteration++;
        uint32_t representative_runs = 0;
        uint32_t remaining_mods = 0;
        bool iteration_aborted = false;
        int64_t iteration_deadline = forkserver_iteration_deadline_us();
        bool *uncovered = NULL;
        bool *executed = NULL;
        SnapshotExitInfo baseline_exit = {0};
        bool baseline_exit_valid = false;

        if (binradar_mode && iteration > 1) {
            uncovered = g_new0(bool, binradar_manager->patch_max_id + 1u);
            executed = g_new0(bool, binradar_manager->patch_max_id + 1u);
            for (uint32_t i = 0; i < binradar_manager->patch_cnt; i++) {
                uint32_t patch = (uint32_t)binradar_manager_patch_id_at(
                    binradar_manager, i + 1u);
                uncovered[patch] = true;
            }
        }

        uint32_t selected_patch = 0;
        for (;;) {
            uint32_t child_status = 0;
            if (binradar_mode) {
                binradar_manager_reset_capture(binradar_manager);
                if (!binradar_publish_selector(binradar_manager,
                                                selected_patch, iteration)) {
                    log_msg("[binradar] [cache-fatal] "
                            "[reason selector-publication]\n");
                    exit_with_status(5);
                }
                if (shared_trace_data != NULL) {
                    memset(&shared_trace_data->exit_info, 0,
                           sizeof(shared_trace_data->exit_info));
                }
                log_msg("[binradar] [shm] [patch-id %u] [iter %u]\n",
                        selected_patch, iteration);
            }

            fflush(NULL);
            trace_mem_flush();
            log_msg_flush();
            if (g_osprey_ctx != NULL && g_osprey_shared_run != NULL) {
                osprey_shared_run_prepare(g_osprey_ctx, g_osprey_shared_run,
                                          iteration);
            }
            snapshot_prepare_mutation_epoch();
            pid_t child_pid = fork();
            if (child_pid < 0) exit_with_status(4);
            if (child_pid == 0) {
#ifdef SNAPSHOT_DEBUG
                snapshot_install_crash_handler();
#endif
                snapshot_modify_memory(cpu_env);
                provenance_clear_pending_fault();
                if (g_osprey_ctx != NULL && g_osprey_shared_run != NULL) {
                    osprey_child_use_shared_run(g_osprey_ctx,
                                                g_osprey_shared_run);
                }
                afl_fork_child = 1;
                close(binradar_forkserver_ctrl_r);
                close(binradar_forkserver_stat_w);
                return;
            }

            representative_runs++;
            int wait_rc = wait_child_and_drain_patch(
                child_pid, &child_status, iteration_deadline);
            if (wait_rc < 0) exit_with_status(6);
            if (wait_rc > 0) {
                consecutive_child_timeouts++;
                log_msg("[forkserver] [child-timeout] [consecutive %d]\n",
                        consecutive_child_timeouts);
            } else {
                consecutive_child_timeouts = 0;
            }
            if (wait_rc == 2 ||
                (abort_after_timeouts > 0 &&
                 consecutive_child_timeouts >= abort_after_timeouts)) {
                log_msg("[forkserver] [abort] [consecutive-timeout %d] "
                        "[iter %u] [runs %u]\n",
                        consecutive_child_timeouts, iteration,
                        representative_runs);
                iteration_aborted = true;
                break;
            }
            trace_mem_flush();

            SnapshotExitInfo *exit_info = snapshot_exit_info_ptr();
            if (binradar_mode && (exit_info == NULL || !exit_info->valid)) {
                log_msg("[binradar] [iteration-discarded] [iter %u] "
                        "[reason unusable-exit] [patch %u]\n",
                        iteration, selected_patch);
                iteration_aborted = true;
                break;
            }
            if (binradar_mode) {
                binradar_record_outcome(binradar_manager, selected_patch);
                if (executed != NULL && selected_patch != 0) {
                    executed[selected_patch] = true;
                }
            }
            if (binradar_mode && selected_patch == 0) {
                baseline_exit = *exit_info;
                baseline_exit_valid = true;
            }

            if (wait_rc == 0 && g_osprey_ctx != NULL &&
                g_osprey_shared_run != NULL && g_osprey_ctx->config.enabled &&
                binradar_mode && iteration == 1 && selected_patch == 0) {
                OspreyStatus merged = osprey_parent_merge_sample(
                    g_osprey_ctx, g_osprey_shared_run);
                if (merged != OSPREY_OK && merged != OSPREY_DISABLED) {
                    log_msg("[forkserver] [osprey] [merge-failed] "
                            "[status %d]\n", (int)merged);
                }
            }

            if (binradar_mode && binradar_manager->cache_enabled) {
                PatchedResult *observed = get_patched_result_tmp(
                    binradar_manager, selected_patch);
                GArray *selected_vector = NULL;
                bool selected_valid =
                    !binradar_manager->cache_capture_overflow &&
                    binradar_cache_vector(binradar_manager, selected_patch,
                                          selected_patch,
                                          &selected_vector) &&
                    binradar_observed_vector_matches(observed->br_taken,
                                                     selected_vector);
                if (!selected_valid) {
                    if (selected_vector != NULL) {
                        g_array_free(selected_vector, TRUE);
                    }
                    if (binradar_manager->feedback_dir != NULL) {
                        log_msg("[binradar] [feedback] [error snapshot] "
                                "[iter %u] [patch %u]\n",
                                iteration, selected_patch);
                        exit_with_status(1);
                    }
                    if (binradar_manager->cache_inference_enabled) {
                        binradar_cache_disable(binradar_manager,
                                               "representative-mismatch");
                        binradar_restore_uncached_candidates(
                            binradar_manager, uncovered, executed);
                    }
                } else {
                    if (!binradar_feedback_write(binradar_manager, iteration,
                                                 selected_patch,
                                                 selected_vector)) {
                        g_array_free(selected_vector, TRUE);
                        exit_with_status(1);
                    }
                    if (binradar_manager->cache_inference_enabled &&
                        iteration > 1) {
                        for (uint32_t i = 0;
                             i < binradar_manager->patch_cnt; i++) {
                            uint32_t candidate =
                                (uint32_t)binradar_manager_patch_id_at(
                                    binradar_manager, i + 1u);
                            if (!uncovered[candidate] ||
                                candidate == selected_patch) continue;
                            GArray *candidate_vector = NULL;
                            if (!binradar_cache_vector(
                                    binradar_manager, selected_patch,
                                    candidate, &candidate_vector)) {
                                binradar_cache_disable(
                                    binradar_manager,
                                    "candidate-evaluation");
                                binradar_restore_uncached_candidates(
                                    binradar_manager, uncovered, executed);
                                break;
                            }
                            if (binradar_observed_vector_matches(
                                    observed->br_taken, candidate_vector)) {
                                binradar_materialize_cache_hit(
                                    binradar_manager, candidate,
                                    selected_patch, candidate_vector);
                                uncovered[candidate] = false;
                            }
                            g_array_free(candidate_vector, TRUE);
                        }
                    }
                    g_array_free(selected_vector, TRUE);
                }
            }

            if (!binradar_mode || iteration == 1) break;
            if (selected_patch != 0) uncovered[selected_patch] = false;
            selected_patch = 0;
            for (uint32_t i = 0; i < binradar_manager->patch_cnt; i++) {
                uint32_t candidate =
                    (uint32_t)binradar_manager_patch_id_at(
                        binradar_manager, i + 1u);
                if (uncovered[candidate]) {
                    selected_patch = candidate;
                    break;
                }
            }
            if (selected_patch == 0) break;
        }

        if (binradar_mode) {
            if (iteration_aborted || !baseline_exit_valid) {
                binradar_clear_current(binradar_manager);
                remaining_mods = 0;
            } else {
                *snapshot_exit_info_ptr() = baseline_exit;
                if (iteration == 1) {
                    if (g_osprey_ctx != NULL && g_osprey_ctx->config.enabled &&
                        osprey_tx_ok(g_osprey_ctx)) {
                        if (!snapshot_test_install_applied_model()) {
                            osprey_analyze(g_osprey_ctx);
                        }
                    }
                    remaining_mods = analyze_collected_data(
                        arg_info, num_arg_regs);
                } else {
                    binradar_commit(binradar_manager);
                    remaining_mods = analyze_collected_data(
                        arg_info, num_arg_regs);
                }
                if (iteration == 1) {
                    binradar_commit(binradar_manager);
                }
            }
        }
        g_free(executed);
        g_free(uncovered);

        uint32_t summary[3] = {
            iteration,
            representative_runs,
            remaining_mods,
        };
        if (write_exact(binradar_forkserver_stat_w, summary,
                        sizeof(summary)) < 0) {
            exit_with_status(7);
        }
    }
}

SnapshotMemRegion *mr_manager_heap_search_pub(target_ulong addr) { return mr_manager_heap_search(addr); }
