/*
 * provenance.c — Runtime pointer-provenance shadow state for heap OOB/UAF.
 *
 * Tags are keyed by guest architectural register number and by guest-memory
 * address (for pointer spills), not by TCG temp index.  This makes tags
 * survive TB boundaries.  The shadow is allocated lazily per CPUArchState
 * and inherits through fork copy-on-write.
 */
#include "qemu/osdep.h"
#include "cpu.h"
#include "snapshot.h"
#include "provenance.h"
#include "tcg/symbolic/symbolic-struct.h"
#include "exec/helper-head.h"
#include "qemu/atomic.h"
#include "qemu/bswap.h"
#include "elf.h"

int provenance_debug = 0;

/* ---- Allocation object table ---- */

/* Object identity counter.  Monotonic; never reused. */
static uint64_t prov_next_object_id = 1;

typedef struct {
    uint64_t object_id;
    uint32_t generation;
} ObjKey;
static GHashTable *prov_object_table = NULL;   /* ObjKey → ProvenanceObject* */
static GHashTable *prov_live_by_base = NULL;   /* base → ObjKey* (LIVE only) */

/* Solver pool cursors (shared/fork-inherited): captured as stable indices at
 * finding time so the timeout path can reconstruct the finding boundary.
 * Declarations come from symbolic-struct.h (included above); the code range
 * comes from symbolic-instrumentation.h. */
extern Query *next_query;
extern Query *query_queue;
extern int symbolic_mode;
extern uint64_t symbolic_start_code;
extern uint64_t symbolic_end_code;

/* Per-run pending fault.  Stored inside SharedTraceData (the shared mmap)
 * so the parent can read it after waitpid even when the child was killed
 * or hit the forkserver timeout; set via provenance_set_shared_fault_ptr
 * from snapshot_init right after the shared mapping is created. */
static PendingProvenanceFault *prov_pending_fault = NULL;

/* Findings recorded before the process reaches BINRADAR_ENTRYPOINT execute in
 * the pre-snapshot prefix.  A whole-run reference pass (PROBE, artifact
 * preflight) starts at the ELF entry and would otherwise publish such an event
 * as the POC identity, but every forkserver child resumes at the
 * patch-function entry — the snapshot precedes that instruction — and can
 * never re-execute the prefix.  Such an identity can therefore never be
 * reproduced, so `same-fault` would be unreachable by construction rather than
 * by filtering.  Prefix events are reported for diagnosis and excluded from
 * the reference.  With no configured entrypoint there is no window definition
 * and behavior is unchanged. */
static bool prov_prefix_finding_logged;

void provenance_set_shared_fault_ptr(PendingProvenanceFault *ptr) {
    prov_pending_fault = ptr;
}

/* ---- Memory shadow ---- */
/* Hash table: aligned 8-byte guest address → PtrMemEntry.
 * We keep entries for all aligned pointer-sized slots. */
static GHashTable *prov_mem_shadow = NULL;

/* ---- Helpers ---- */

static guint obj_key_hash(gconstpointer key) {
    const ObjKey *k = key;
    return (guint)(k->object_id ^ (k->object_id >> 32) ^ k->generation);
}

static gboolean obj_key_equal(gconstpointer a, gconstpointer b) {
    const ObjKey *ka = a, *kb = b;
    return ka->object_id == kb->object_id && ka->generation == kb->generation;
}

static ObjKey *obj_key_new(uint64_t id, uint32_t gen) {
    ObjKey *k = g_new(ObjKey, 1);
    k->object_id = id;
    k->generation = gen;
    return k;
}

static void obj_value_destroy(gpointer data) {
    g_free(data);
}

static void obj_key_destroy(gpointer data) {
    g_free(data);
}

static void prov_ensure_tables(void) {
    if (prov_object_table == NULL) {
        prov_object_table = g_hash_table_new_full(obj_key_hash, obj_key_equal,
                                                   obj_key_destroy,
                                                   obj_value_destroy);
    }
    if (prov_live_by_base == NULL) {
        prov_live_by_base = g_hash_table_new_full(g_direct_hash, g_direct_equal,
                                                   NULL, obj_key_destroy);
    }
    if (prov_mem_shadow == NULL) {
        prov_mem_shadow = g_hash_table_new_full(g_direct_hash, g_direct_equal,
                                                 NULL, g_free);
    }
}

/* ---- Initialization ---- */

/* Synchronization and support boundary:
 * - Forkserver children have private COW copies of these tables, so there is
 *   no cross-process sharing between iterations.
 * - Provenance/memcheck is supported only for single-threaded guests, matching
 *   Fuzzolic's concolic engine and the benchmark corpus.  QEMU linux-user can
 *   execute CLONE_VM guests on multiple host threads, but these process-global
 *   GLib tables are not synchronized and register shadows are not inherited
 *   across clone.  Findings from multithreaded guests are therefore outside
 *   the supported contract and must not be used as correctness evidence.
 * - Supporting multithreaded guests in the future requires an explicit design
 *   for register-shadow inheritance, shared-table synchronization, and atomic
 *   finding publication before enabling that mode. */
void provenance_init(void) {
    prov_ensure_tables();
    if (prov_pending_fault) {
        memset(prov_pending_fault, 0, sizeof(*prov_pending_fault));
    }
    const char *dbg = getenv("BINRADAR_PROVENANCE_DEBUG");
    if (dbg) {
        provenance_debug = atoi(dbg) != 0;
    }
}

/* Per-CPU register shadow is stored as a pointer at a fixed offset in
 * CPUArchState.  We use a GHashTable keyed by env pointer for simplicity
 * and to avoid modifying the CPUX86State struct.  For single-threaded
 * guest programs (the common case in this tracer), this is equivalent. */
static GHashTable *prov_reg_shadows = NULL;  /* env* → PtrRegShadow* */

PtrRegShadow *provenance_get_reg_shadow(CPUArchState *env) {
    if (prov_reg_shadows == NULL) {
        prov_reg_shadows = g_hash_table_new_full(g_direct_hash, g_direct_equal,
                                                  NULL, g_free);
    }
    PtrRegShadow *shadow = g_hash_table_lookup(prov_reg_shadows, env);
    if (shadow == NULL) {
        shadow = g_new0(PtrRegShadow, 1);
        g_hash_table_insert(prov_reg_shadows, env, shadow);
    }
    return shadow;
}

/* ---- Allocation object management ---- */

PtrTag provenance_create_object(target_ulong base, target_ulong size,
                                target_ulong pc, PtrProducerKind kind) {
    prov_ensure_tables();
    uint64_t id = prov_next_object_id++;
    uint32_t gen = 1;

    /* Check if there was a previous object at this base.  If so, its
     * generation was already retired.  We use a new generation for the
     * new object so stale pointers to the old object report UAF. */
    ObjKey *old_key = g_hash_table_lookup(prov_live_by_base,
                                          GINT_TO_POINTER((uintptr_t)base));
    (void)old_key;  /* old LIVE object at this base should have been retired */

    ProvenanceObject *obj = g_new(ProvenanceObject, 1);
    obj->object_id = id;
    obj->generation = gen;
    obj->base = base;
    obj->requested_size = size;
    obj->alloc_pc = pc;
    obj->state = PROV_OBJ_LIVE;

    ObjKey *key = obj_key_new(id, gen);
    g_hash_table_insert(prov_object_table, key, obj);
    g_hash_table_insert(prov_live_by_base,
                        GINT_TO_POINTER((uintptr_t)base), obj_key_new(id, gen));

    PtrTag tag = {
        .object_id = id,
        .generation = gen,
        .concrete_offset = 0,
        .concrete_value = base,
        .producer_pc = pc,
        .producer_kind = kind,
        .valid = true,
    };
    return tag;
}

bool provenance_retire_object(target_ulong base) {
    prov_ensure_tables();
    ObjKey *key = g_hash_table_lookup(prov_live_by_base,
                                      GINT_TO_POINTER((uintptr_t)base));
    if (key == NULL) {
        return false;
    }
    ProvenanceObject *obj = g_hash_table_lookup(prov_object_table, key);
    if (obj == NULL) {
        return false;
    }
    obj->state = PROV_OBJ_FREED;
    /* Remove from live-by-base but keep in object table (for UAF). */
    g_hash_table_steal(prov_live_by_base, GINT_TO_POINTER((uintptr_t)base));
    /* The ObjKey* was stolen — free it manually. */
    g_free(key);
    return true;
}

ProvenanceObject *provenance_lookup_object(uint64_t object_id,
                                           uint32_t generation) {
    if (prov_object_table == NULL) return NULL;
    ObjKey key = { .object_id = object_id, .generation = generation };
    return g_hash_table_lookup(prov_object_table, &key);
}

ProvenanceObject *provenance_lookup_live_by_base(target_ulong base) {
    if (prov_live_by_base == NULL) return NULL;
    ObjKey *key = g_hash_table_lookup(prov_live_by_base,
                                      GINT_TO_POINTER((uintptr_t)base));
    if (key == NULL) return NULL;
    return g_hash_table_lookup(prov_object_table, key);
}

/* ---- Pending allocator operations (per-CPU) ---- */

void provenance_set_pending(CPUArchState *env, ProvenancePendingKind kind,
                            target_ulong call_pc, target_ulong arg_size,
                            target_ulong arg_ptr) {
    prov_ensure_tables();
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    memset(&shadow->pending, 0, sizeof(shadow->pending));
    shadow->pending.valid = true;
    shadow->pending.kind = kind;
    shadow->pending.call_pc = call_pc;
    shadow->pending.arg_size = arg_size;
    shadow->pending.arg_ptr = arg_ptr;
    shadow->pending.old_object_id = 0;
    shadow->pending.old_generation = 0;
    shadow->pending.calloc_count = 0;
    shadow->pending.calloc_element_size = 0;
}

ProvenancePending provenance_get_pending(CPUArchState *env,
                                         target_ulong call_pc) {
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    if (shadow->pending.valid && shadow->pending.call_pc == call_pc) {
        return shadow->pending;
    }
    ProvenancePending empty = {0};
    return empty;
}

void provenance_clear_pending(CPUArchState *env) {
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    memset(&shadow->pending, 0, sizeof(shadow->pending));
}

/* ---- Register tag operations ---- */

void provenance_invalidate_reg(CPUArchState *env, int reg_idx,
                               target_ulong pc) {
    if (reg_idx < 0 || reg_idx >= CPU_NB_REGS) return;
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    shadow->gpr[reg_idx].valid = false;
    shadow->last_writer_pc[reg_idx] = pc;
}

/* Signal delivery/return and other wholesale context switches overwrite
 * every GPR with context values: invalidate all register tags. */
void provenance_invalidate_all_regs(CPUArchState *env) {
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    for (int i = 0; i < CPU_NB_REGS; i++) {
        shadow->gpr[i].valid = false;
    }
}

void provenance_set_reg_tag(CPUArchState *env, int reg_idx, PtrTag tag) {
    if (reg_idx < 0 || reg_idx >= CPU_NB_REGS) return;
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    shadow->gpr[reg_idx] = tag;
    shadow->last_writer_pc[reg_idx] = tag.producer_pc;
}

PtrTag provenance_get_reg_tag(CPUArchState *env, int reg_idx) {
    if (reg_idx < 0 || reg_idx >= CPU_NB_REGS) {
        PtrTag unknown = {0};
        return unknown;
    }
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    return shadow->gpr[reg_idx];
}

void provenance_propagate_mov(CPUArchState *env, int dst_idx, int src_idx,
                              target_ulong pc, target_ulong src_val,
                              target_ulong dst_val) {
    if (dst_idx < 0 || dst_idx >= CPU_NB_REGS) return;
    if (src_idx < 0 || src_idx >= CPU_NB_REGS) return;
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    PtrTag src_tag = shadow->gpr[src_idx];
    /* Value-consistency: concrete_value must match the actual register. */
    if (src_tag.valid && src_tag.concrete_value == src_val) {
        src_tag.concrete_value = dst_val;
        src_tag.producer_pc = pc;
        src_tag.producer_kind = PROV_PRODUCER_MOV;
        shadow->gpr[dst_idx] = src_tag;
    } else {
        shadow->gpr[dst_idx].valid = false;
    }
    shadow->last_writer_pc[dst_idx] = pc;
}

void provenance_lea_imm(CPUArchState *env, int dst_idx, int base_idx,
                        int64_t disp, target_ulong pc,
                        target_ulong dst_val, target_ulong base_val) {
    if (dst_idx < 0 || dst_idx >= CPU_NB_REGS) return;
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    if (base_idx < 0 || base_idx >= CPU_NB_REGS) {
        shadow->gpr[dst_idx].valid = false;
        shadow->last_writer_pc[dst_idx] = pc;
        return;
    }
    PtrTag base_tag = shadow->gpr[base_idx];
    if (!base_tag.valid ||
        base_tag.concrete_value != base_val) {
        shadow->gpr[dst_idx].valid = false;
        shadow->last_writer_pc[dst_idx] = pc;
        return;
    }
    /* Checked offset arithmetic: offset + disp (overflow-safe). */
    int64_t new_offset;
    if (__builtin_add_overflow(base_tag.concrete_offset, disp, &new_offset)) {
        shadow->gpr[dst_idx].valid = false;
        shadow->last_writer_pc[dst_idx] = pc;
        return;
    }
    PtrTag dst_tag = base_tag;
    dst_tag.concrete_offset = new_offset;
    dst_tag.concrete_value = dst_val;
    dst_tag.producer_pc = pc;
    dst_tag.producer_kind = PROV_PRODUCER_LEA;
    shadow->gpr[dst_idx] = dst_tag;
    shadow->last_writer_pc[dst_idx] = pc;
}

void provenance_addsub_imm(CPUArchState *env, int reg_idx, int64_t delta,
                           target_ulong pc, target_ulong pre_val,
                           target_ulong post_val) {
    if (reg_idx < 0 || reg_idx >= CPU_NB_REGS) return;
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    PtrTag tag = shadow->gpr[reg_idx];
    if (!tag.valid || tag.concrete_value != pre_val) {
        shadow->gpr[reg_idx].valid = false;
        shadow->last_writer_pc[reg_idx] = pc;
        return;
    }
    int64_t new_offset;
    if (__builtin_add_overflow(tag.concrete_offset, delta, &new_offset)) {
        shadow->gpr[reg_idx].valid = false;
        shadow->last_writer_pc[reg_idx] = pc;
        return;
    }
    tag.concrete_offset = new_offset;
    tag.concrete_value = post_val;
    tag.producer_pc = pc;
    tag.producer_kind = (delta >= 0) ? PROV_PRODUCER_ADD_IMM
                                     : PROV_PRODUCER_SUB_IMM;
    shadow->gpr[reg_idx] = tag;
    shadow->last_writer_pc[reg_idx] = pc;
}

/* ---- reg-reg ADD/SUB provenance propagation ----
 * Runs AFTER the ALU write-back (gen_op has already written dst and
 * invalidated its tag).  dst holds the result; src is unchanged.
 * Only these sound forms propagate (§6):
 *   dst tagged, src untagged: dst = dst ± src.  The exact target-width
 *     result must match, and the tracked offset folds the signed source
 *     value with checked overflow arithmetic.
 *   dst untagged, src tagged, ADD: dst = src + dst.  The source value
 *     must match its tag and the target-width delta is folded into the
 *     offset with checked overflow arithmetic.
 * Both tagged operands, or SUB of a pointer from a non-pointer, have no
 * sound merge rule and invalidate. */
void provenance_addsub_reg(CPUArchState *env, int dst_idx, int src_idx,
                           int is_sub, target_ulong pc,
                           target_ulong dst_val, target_ulong src_val) {
    if (dst_idx < 0 || dst_idx >= CPU_NB_REGS) return;
    if (src_idx < 0 || src_idx >= CPU_NB_REGS) return;
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    PtrTag dst_tag = shadow->gpr[dst_idx];
    PtrTag src_tag = shadow->gpr[src_idx];
    if (dst_tag.valid && !src_tag.valid) {
        target_ulong expect = is_sub
            ? dst_tag.concrete_value - src_val
            : dst_tag.concrete_value + src_val;
        int64_t signed_src = (int64_t)src_val;
        int64_t delta = signed_src;
        if (expect != dst_val ||
            (is_sub && __builtin_sub_overflow((int64_t)0, signed_src,
                                              &delta))) {
            shadow->gpr[dst_idx].valid = false;
            shadow->last_writer_pc[dst_idx] = pc;
            return;
        }
        int64_t new_offset;
        if (__builtin_add_overflow(dst_tag.concrete_offset, delta,
                                   &new_offset)) {
            shadow->gpr[dst_idx].valid = false;
            shadow->last_writer_pc[dst_idx] = pc;
            return;
        }
        dst_tag.concrete_offset = new_offset;
        dst_tag.concrete_value = dst_val;
        dst_tag.producer_pc = pc;
        dst_tag.producer_kind = (delta >= 0) ? PROV_PRODUCER_ADD_IMM
                                             : PROV_PRODUCER_SUB_IMM;
        shadow->gpr[dst_idx] = dst_tag;
        shadow->last_writer_pc[dst_idx] = pc;
        return;
    }
    if (!dst_tag.valid && src_tag.valid && !is_sub) {
        /* ADD with dst the untagged offset and src the pointer. */
        target_ulong delta_bits = dst_val - src_val;
        int64_t delta = (int64_t)delta_bits;
        if (src_tag.concrete_value != src_val) {
            shadow->gpr[dst_idx].valid = false;
            shadow->last_writer_pc[dst_idx] = pc;
            return;
        }
        int64_t new_offset;
        if (__builtin_add_overflow(src_tag.concrete_offset, delta,
                                   &new_offset)) {
            shadow->gpr[dst_idx].valid = false;
            shadow->last_writer_pc[dst_idx] = pc;
            return;
        }
        src_tag.concrete_offset = new_offset;
        src_tag.concrete_value = dst_val;
        src_tag.producer_pc = pc;
        src_tag.producer_kind = PROV_PRODUCER_ADD_IMM;
        shadow->gpr[dst_idx] = src_tag;
        shadow->last_writer_pc[dst_idx] = pc;
        return;
    }
    /* both tagged, or SUB of a pointer from a non-pointer: not soundly
     * derivable. */
    shadow->gpr[dst_idx].valid = false;
    shadow->last_writer_pc[dst_idx] = pc;
}

void provenance_clobber_caller_saved(CPUArchState *env) {
    /* x86-64 ABI: RAX, RCX, RDX, RSI, RDI, R8-R11 are caller-saved. */
    static const int caller_saved[] = {
        R_EAX, R_ECX, R_EDX, R_ESI, R_EDI,
        R_R8, R_R9, R_R10, R_R11,
    };
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    for (size_t i = 0; i < sizeof(caller_saved)/sizeof(caller_saved[0]); i++) {
        shadow->gpr[caller_saved[i]].valid = false;
    }
}

/* ---- Memory shadow operations ---- */

void provenance_mem_store_tag(target_ulong addr, PtrTag tag) {
    if (prov_mem_shadow == NULL) prov_ensure_tables();
    /* Only full aligned slots are tracked; an unaligned store must not
     * alias the aligned slot (the bytes there are not this tag's value). */
    if ((addr & (sizeof(target_ulong) - 1)) != 0) {
        return;
    }
    if (tag.valid) {
        PtrMemEntry *entry = g_new(PtrMemEntry, 1);
        entry->addr = addr;
        entry->tag = tag;
        g_hash_table_replace(prov_mem_shadow,
                             GINT_TO_POINTER((uintptr_t)addr), entry);
    } else {
        g_hash_table_remove(prov_mem_shadow,
                            GINT_TO_POINTER((uintptr_t)addr));
    }
}

PtrTag provenance_mem_load_tag(target_ulong addr) {
    PtrTag unknown = {0};
    if (prov_mem_shadow == NULL) {
        return unknown;
    }
    /* Unaligned native-width load: the shadow only tracks full aligned
     * slots; aligning down would return the wrong slot's tag.  Refuse
     * (UNKNOWN) instead of guessing. */
    if ((addr & (sizeof(target_ulong) - 1)) != 0) {
        return unknown;
    }
    PtrMemEntry *entry = g_hash_table_lookup(prov_mem_shadow,
                                             GINT_TO_POINTER((uintptr_t)addr));
    if (entry == NULL) {
        return unknown;
    }
    /* Value-consistency: the saved concrete value must match the bytes
     * actually at this address.  The caller must verify this. */
    return entry->tag;
}

void provenance_mem_invalidate(target_ulong addr, target_ulong size) {
    if (prov_mem_shadow == NULL) return;
    if (size == 0) return;
    /* Overflow-safe interval: [addr, addr+size) may wrap in the guest
     * address space.  A wrapped range is bogus (no real mapping spans the
     * address-space wrap); invalidate only the aligned slots actually
     * touched before the wrap and stop — never sweep to UINT64_MAX. */
    target_ulong start = addr & ~(target_ulong)(sizeof(target_ulong) - 1);
    target_ulong last = addr + size - 1;
    target_ulong end;
    if (last < addr) {
        end = (target_ulong)-1 - sizeof(target_ulong) + 1;  /* clamp: no wrap */
        /* The range is invalid; invalidate just the start slot. */
        g_hash_table_remove(prov_mem_shadow,
                            GINT_TO_POINTER((uintptr_t)start));
        return;
    }
    end = last & ~(target_ulong)(sizeof(target_ulong) - 1);
    for (target_ulong a = start;;) {
        g_hash_table_remove(prov_mem_shadow,
                            GINT_TO_POINTER((uintptr_t)a));
        if (a == end) break;
        /* Stop before a wraps or passes end. */
        if (a > end - sizeof(target_ulong)) break;
        a += sizeof(target_ulong);
    }
}

/* ---- Access checking ---- */

typedef struct {
    uint64_t file_start;
    uint64_t file_end;
    uint64_t virtual_start;
} ProvExecSegment;

typedef struct {
    struct stat stamp;
    uint8_t image_id[32];
    GArray *segments;
    bool hashed;
    bool verified;
    bool tainted;
} ProvImageIdentity;

typedef struct {
    target_ulong start;
    target_ulong end;
    bool runtime;
    ProvImageIdentity *image;
    uint64_t image_bias;
    bool site_valid;
} ProvCodeMapping;

static GArray *prov_code_mappings;
static GPtrArray *prov_images;

static bool prov_same_image_stamp(const struct stat *a, const struct stat *b)
{
    return a->st_dev == b->st_dev && a->st_ino == b->st_ino &&
           a->st_size == b->st_size &&
           a->st_mtim.tv_sec == b->st_mtim.tv_sec && a->st_mtim.tv_nsec == b->st_mtim.tv_nsec &&
           a->st_ctim.tv_sec == b->st_ctim.tv_sec && a->st_ctim.tv_nsec == b->st_ctim.tv_nsec;
}

static ProvImageIdentity *prov_image_identity(int fd)
{
    struct stat stamp;
    if (fstat(fd, &stamp) != 0 || !S_ISREG(stamp.st_mode) || stamp.st_size < sizeof(Elf64_Ehdr)) return NULL;
    if (prov_images == NULL) prov_images = g_ptr_array_new();
    for (unsigned i = 0; i < prov_images->len; i++) {
        ProvImageIdentity *image = g_ptr_array_index(prov_images, i);
        if (prov_same_image_stamp(&image->stamp, &stamp)) return image;
    }
    Elf64_Ehdr header;
    if (pread(fd, &header, sizeof(header), 0) != sizeof(header) ||
        memcmp(header.e_ident, ELFMAG, SELFMAG) != 0 ||
        header.e_ident[EI_CLASS] != ELFCLASS64 || header.e_ident[EI_DATA] != ELFDATA2LSB ||
        le16_to_cpu(header.e_machine) != EM_X86_64 ||
        le16_to_cpu(header.e_phentsize) != sizeof(Elf64_Phdr)) return NULL;
    uint64_t offset = le64_to_cpu(header.e_phoff);
    uint16_t count = le16_to_cpu(header.e_phnum);
    if (offset > stamp.st_size || (uint64_t)count * sizeof(Elf64_Phdr) > (uint64_t)stamp.st_size - offset) return NULL;
    ProvImageIdentity *image = g_new0(ProvImageIdentity, 1);
    image->stamp = stamp;
    image->segments = g_array_new(false, false, sizeof(ProvExecSegment));
    for (unsigned i = 0; i < count; i++) {
        Elf64_Phdr program;
        if (pread(fd, &program, sizeof(program), offset + i * sizeof(program)) != sizeof(program)) {
            g_array_free(image->segments, true);
            g_free(image);
            return NULL;
        }
        if (le32_to_cpu(program.p_type) != PT_LOAD || !(le32_to_cpu(program.p_flags) & PF_X)) continue;
        uint64_t file_start = le64_to_cpu(program.p_offset);
        uint64_t file_size = le64_to_cpu(program.p_filesz);
        uint64_t virtual_start = le64_to_cpu(program.p_vaddr);
        if (file_start > stamp.st_size || file_size > (uint64_t)stamp.st_size - file_start ||
            (file_start & ~TARGET_PAGE_MASK) != (virtual_start & ~TARGET_PAGE_MASK)) continue;
        ProvExecSegment segment = {file_start & TARGET_PAGE_MASK,
            file_start + file_size, virtual_start & TARGET_PAGE_MASK};
        g_array_append_val(image->segments, segment);
    }
    g_ptr_array_add(prov_images, image);
    return image;
}

static void prov_image_hash(ProvImageIdentity *image, int fd)
{
    if (image->hashed) return;
    image->hashed = true;
    GChecksum *checksum = g_checksum_new(G_CHECKSUM_SHA256);
    uint8_t bytes[8192];
    off_t offset = 0;
    while (offset < image->stamp.st_size) {
        size_t wanted = MIN(sizeof(bytes), image->stamp.st_size - offset);
        ssize_t count = pread(fd, bytes, wanted, offset);
        if (count <= 0) break;
        g_checksum_update(checksum, bytes, count);
        offset += count;
    }
    struct stat after;
    if (offset == image->stamp.st_size && fstat(fd, &after) == 0 &&
        prov_same_image_stamp(&image->stamp, &after)) {
        gsize digest_size = sizeof(image->image_id);
        g_checksum_get_digest(checksum, image->image_id, &digest_size);
        image->verified = digest_size == sizeof(image->image_id);
    }
    g_checksum_free(checksum);
    if (!image->verified) log_msg("[memcheck] [coverage] [unverified-image]\n");
}

static bool prov_main_pc(target_ulong pc)
{
    return symbolic_start_code > 0 && pc >= symbolic_start_code &&
           pc < symbolic_end_code;
}

void provenance_memcheck_unmap(target_ulong addr, target_ulong size)
{
    if (prov_code_mappings == NULL || size == 0 || addr > (target_ulong)-1 - size) {
        return;
    }
    target_ulong end = addr + size;
    for (unsigned i = 0; i < prov_code_mappings->len;) {
        ProvCodeMapping *range = &g_array_index(prov_code_mappings, ProvCodeMapping, i);
        if (range->end <= addr || range->start >= end) {
            i++;
            continue;
        }
        if (range->start < addr && range->end > end) {
            ProvCodeMapping right = *range;
            right.start = end;
            range->end = addr;
            g_array_insert_val(prov_code_mappings, i + 1, right);
            break;
        }
        if (range->start < addr) {
            range->end = addr;
            i++;
        } else if (range->end > end) {
            range->start = end;
            break;
        } else {
            g_array_remove_index(prov_code_mappings, i);
        }
    }
}

void provenance_memcheck_protect(target_ulong addr, target_ulong size, int prot)
{
    if (!(prot & PROT_WRITE) || prov_code_mappings == NULL ||
        size == 0 || addr > (target_ulong)-1 - size) return;
    target_ulong end = addr + size;
    for (unsigned i = 0; i < prov_code_mappings->len; i++) {
        ProvCodeMapping *range = &g_array_index(prov_code_mappings, ProvCodeMapping, i);
        if (range->site_valid && range->start < end && range->end > addr) {
            range->image->tainted = true;
        }
    }
}

void provenance_memcheck_mapping(target_ulong addr, target_ulong size, int fd,
                                 uint64_t file_offset)
{
    /* Symbolic allocator summaries also need the trusted-runtime boundary;
     * image tracking never enables raw memcheck on its own. */
    if ((!binradar_memcheck_enabled && !symbolic_mode &&
         getenv("BINRADAR_EVIDENCE_FILE") == NULL) ||
        size == 0 || addr > (target_ulong)-1 - size) {
        return;
    }
    provenance_memcheck_unmap(addr, size);
    if (fd < 0) return;
    char fd_name[64], filename[PATH_MAX + 1];
    snprintf(fd_name, sizeof(fd_name), "/proc/self/fd/%d", fd);
    ssize_t length = readlink(fd_name, filename, sizeof(filename) - 1);
    bool runtime = true;
    if (length >= 0 && length < sizeof(filename) - 1) {
        filename[length] = '\0';
        const char *name = strrchr(filename, '/');
        name = name ? name + 1 : filename;
        runtime = strcmp(name, "libc.so.6") == 0 ||
                  strncmp(name, "libc-", 5) == 0 ||
                  strncmp(name, "ld-linux-", 9) == 0 ||
                  strncmp(name, "ld-", 3) == 0;
    } else {
        log_msg("[memcheck] [coverage] [unresolved-image] [addr %lx]\n", addr);
    }
    if (prov_code_mappings == NULL) {
        prov_code_mappings = g_array_new(false, false, sizeof(ProvCodeMapping));
    }
    ProvCodeMapping range = {.start = addr, .end = addr + size, .runtime = runtime};
    range.image = prov_image_identity(fd);
    if (range.image != NULL) {
        for (unsigned i = 0; i < range.image->segments->len; i++) {
            const ProvExecSegment *segment = &g_array_index(range.image->segments, ProvExecSegment, i);
            if (file_offset < segment->file_start || file_offset >= segment->file_end) continue;
            uint64_t delta = file_offset - segment->file_start;
            if (segment->virtual_start > addr || delta > addr - segment->virtual_start) continue;
            range.image_bias = addr - segment->virtual_start - delta;
            /* The first main executable mapping precedes main-bound setup;
             * its normalized PCs never need a content-derived identity. */
            if (symbolic_start_code > 0 && !prov_main_pc(addr)) {
                prov_image_hash(range.image, fd);
                range.site_valid = range.image->verified;
            }
            break;
        }
    }
    unsigned index = 0;
    while (index < prov_code_mappings->len &&
           g_array_index(prov_code_mappings, ProvCodeMapping, index).start < addr) index++;
    if (range.site_valid && (page_get_flags(addr) & PAGE_WRITE)) range.image->tainted = true;
    g_array_insert_val(prov_code_mappings, index, range);
}

static const ProvCodeMapping *prov_code_mapping(target_ulong pc)
{
    if (prov_code_mappings == NULL || !(page_get_flags(pc) & PAGE_EXEC)) return NULL;
    unsigned low = 0, high = prov_code_mappings->len;
    while (low < high) {
        unsigned middle = low + (high - low) / 2;
        const ProvCodeMapping *range = &g_array_index(prov_code_mappings, ProvCodeMapping, middle);
        if (pc < range->start) high = middle;
        else if (pc >= range->end) low = middle + 1;
        else return range;
    }
    return NULL;
}

bool provenance_runtime_pc(target_ulong pc)
{
    const ProvCodeMapping *range = prov_code_mapping(pc);
    return range != NULL && range->runtime && range->site_valid &&
           !range->image->tainted;
}

bool provenance_memcheck_pc_eligible(target_ulong pc)
{
    if (!binradar_memcheck_enabled || is_in_e9_exclude_region(pc)) return false;
    if (prov_main_pc(pc)) return true;
    const ProvCodeMapping *range = prov_code_mapping(pc);
    return range != NULL && !range->runtime && range->site_valid && !range->image->tainted;
}

bool provenance_memcheck_site(target_ulong pc, ProvenanceFaultSite *site)
{
    memset(site, 0, sizeof(*site));
    if (is_in_e9_exclude_region(pc)) return false;
    if (prov_main_pc(pc)) return true;
    const ProvCodeMapping *range = prov_code_mapping(pc);
    if (range == NULL || !range->site_valid || range->image->tainted || pc < range->image_bias) return false;
    site->valid = true;
    memcpy(site->image_id, range->image->image_id, sizeof(site->image_id));
    site->image_offset = pc - range->image_bias;
    return true;
}

static bool prov_caller_reference_pc(CPUArchState *env, target_ulong *reference_pc,
                                     bool main_only)
{
    if (env == NULL) return false;
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    if (shadow->external_call_overflow) {
        if (env->regs[R_ESP] <= shadow->external_overflow_sp) return false;
        shadow->external_call_overflow = false;
    }
    /* A stack unwind invalidates crossed boundaries, never guesses a new
     * caller from arbitrary stack contents. */
    while (shadow->external_call_count &&
           env->regs[R_ESP] > shadow->external_calls[shadow->external_call_count - 1].entry_sp) {
        shadow->external_call_count--;
    }
    for (unsigned count = shadow->external_call_count; count > 0; count--) {
        unsigned index = count - 1;
        target_ulong saved_return;
        if (!access_ok(VERIFY_READ, shadow->external_calls[index].entry_sp,
                       sizeof(saved_return))) return false;
        memcpy(&saved_return, g2h(shadow->external_calls[index].entry_sp),
               sizeof(saved_return));
        if (saved_return != shadow->external_calls[index].return_pc) return false;
        if (!provenance_memcheck_pc_eligible(saved_return)) return false;
        if (main_only && !prov_main_pc(saved_return)) continue;
        *reference_pc = saved_return;
        return true;
    }
    return false;
}

bool provenance_memcheck_reference_pc(CPUArchState *env, target_ulong pc,
                                      target_ulong *reference_pc)
{
    ProvenanceFaultSite site;
    /* Identity proof is separate from raw instrumentation eligibility.
     * Unknown E9 helpers still fail site validation without caller fallback. */
    target_ulong original;
    if (e9_original_instruction_pc(pc, &original)) {
        if (!prov_main_pc(original)) return false;
        pc = original;
    }
    if (!provenance_memcheck_site(pc, &site)) return false;
    if (binradar_memcheck_enabled && site.valid &&
        prov_caller_reference_pc(env, reference_pc, true)) {
        /* Match AFL's innermost main frame, including its return-PC
         * convention. Capture now, not when a deferred finding finalizes. */
        return true;
    }
    /* Main instructions identify themselves. With no validated main frame,
     * retain the verified DSO site rather than inventing a main identity. */
    *reference_pc = pc;
    return true;
}

void provenance_memcheck_call(CPUArchState *env, target_ulong callee_pc,
                              target_ulong entry_sp)
{
    if (!binradar_memcheck_enabled) return;
    /* Main-image PLT calls enter main text before jumping into a DSO, so
     * the observed return boundary matters even when callee_pc is main. */
    (void)callee_pc;
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    if (shadow->external_call_overflow) {
        if (entry_sp < shadow->external_overflow_sp) return;
        shadow->external_call_overflow = false;
    }
    if (!access_ok(VERIFY_READ, entry_sp, sizeof(target_ulong))) return;
    target_ulong return_pc;
    memcpy(&return_pc, g2h(entry_sp), sizeof(return_pc));
    if (!provenance_memcheck_pc_eligible(return_pc)) return;
    while (shadow->external_call_count &&
           entry_sp >= shadow->external_calls[shadow->external_call_count - 1].entry_sp) {
        shadow->external_call_count--;
    }
    if (shadow->external_call_count == ARRAY_SIZE(shadow->external_calls)) {
        shadow->external_call_overflow = true;
        shadow->external_overflow_sp = entry_sp;
        log_msg("[memcheck] [coverage] [call-depth-exhausted]\n");
        return;
    }
    unsigned index = shadow->external_call_count++;
    shadow->external_calls[index].return_pc = return_pc;
    shadow->external_calls[index].entry_sp = entry_sp;
}

void provenance_memcheck_ret(CPUArchState *env, target_ulong pc,
                             target_ulong post_sp)
{
    if (!binradar_memcheck_enabled) return;
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    if (shadow->external_call_overflow && post_sp > shadow->external_overflow_sp) {
        shadow->external_call_overflow = false;
    }
    while (shadow->external_call_count &&
           post_sp > shadow->external_calls[shadow->external_call_count - 1].entry_sp) {
        unsigned index = --shadow->external_call_count;
        if (pc != shadow->external_calls[index].return_pc) {
            /* Nonlocal return: crossed frames are no longer evidence. */
            continue;
        }
    }
}

static bool prov_syscall_read_pc(CPUArchState *env, target_ulong *out)
{
    if (!binradar_memcheck_enabled) return false;
    target_ulong pc = provenance_get_reg_shadow(env)->syscall_pc;
    /* Runtime wrappers check the nearest eligible caller's logical access.
     * Fault publication separately resolves its outer main-image identity. */
    if (!provenance_memcheck_pc_eligible(pc)) {
        if (!prov_caller_reference_pc(env, &pc, false)) return false;
    }
    *out = pc;
    return true;
}

void provenance_check_syscall_read(CPUArchState *env, target_ulong addr,
                                   target_ulong size, int reg)
{
    target_ulong pc;
    if (size == 0 || !prov_syscall_read_pc(env, &pc)) return;
    PtrTag tag = {0};
    target_ulong value = 0;
    if (reg >= 0 && reg < CPU_NB_REGS) {
        tag = provenance_get_reg_tag(env, reg);
        value = env->regs[reg];
        if (tag.valid && tag.concrete_value == value) {
            target_ulong delta = addr >= value ? addr - value : value - addr;
            if (delta > INT64_MAX || (addr >= value
                ? __builtin_add_overflow(tag.concrete_offset, (int64_t)delta,
                                         &tag.concrete_offset)
                : __builtin_sub_overflow(tag.concrete_offset, (int64_t)delta,
                                         &tag.concrete_offset))) {
                tag.valid = false;
            }
        }
    }
    provenance_check_access(env, addr, size, pc, tag, reg, value);
}

void provenance_check_syscall_read_tagged(CPUArchState *env, target_ulong addr,
                                          target_ulong size, PtrTag tag)
{
    target_ulong pc;
    if (size == 0 || !prov_syscall_read_pc(env, &pc)) return;
    if (tag.concrete_value != addr) tag.valid = false;
    provenance_check_access(env, addr, size, pc, tag, -1, addr);
}

/* Publication policy.  A tagged finding is sticky.  It may promote a
 * committed UNKNOWN fallback only for the same PC/address/width.  The two
 * immutable slots ensure a timeout SIGKILL during promotion leaves the
 * fallback intact and readable. */
static ProvPublishedFinding *prov_fault_slot_for_publish(
        PendingProvenanceFault *pf, ProvFindingQuality quality,
        target_ulong pc, target_ulong addr, uint32_t size) {
    if (pf == NULL || atomic_load_acquire(&pf->tagged.ready) != 0) {
        return NULL;
    }

    bool fallback_ready =
        atomic_load_acquire(&pf->fallback.ready) != 0;
    if (!fallback_ready) {
        return quality == PROV_FINDING_TAGGED
            ? &pf->tagged : &pf->fallback;
    }
    if (quality != PROV_FINDING_TAGGED) {
        return NULL;
    }

    const ProvFindingRecord *fallback = &pf->fallback.payload;
    return fallback->actual_pc == pc &&
           fallback->access_addr == addr &&
           fallback->access_width == size
        ? &pf->tagged : NULL;
}

/* Fill one immutable publication slot.  Captures the last writer PC of the
 * tracked base register for observability; 0 when the register is unknown. */
static void prov_fault_fill(PendingProvenanceFault *pf, CPUArchState *env,
                            target_ulong pc, target_ulong addr, uint32_t size,
                            uint64_t obj_id, uint32_t gen,
                            target_ulong obj_base, target_ulong obj_size,
                            int64_t offset, target_ulong producer_pc,
                            PtrProducerKind producer_kind, int ea_base_reg,
                            target_ulong ea_base_reg_val, bool is_uaf,
                            ProvFindingQuality quality) {
    target_ulong reference_pc;
    if (!provenance_memcheck_reference_pc(env, pc, &reference_pc)) {
        log_msg("[memcheck] [unclassified-access] [actual_pc %lx] [addr %lx] [width %u]\n",
                pc, addr, size);
        return;
    }
    /* A pre-entry event lies outside every forkserver child's executable
     * window (the snapshot precedes the entrypoint instruction).  Publish it
     * as a diagnostic only: it is not reproducible by the sweep, so using it
     * as the reference would make `same-fault` unreachable by construction. */
    if (pf == prov_pending_fault && binradar_entrypoint != (target_ulong)-1 &&
        !binradar_entrypoint_reached) {
        if (!prov_prefix_finding_logged) {
            prov_prefix_finding_logged = true;
            log_msg("[prov] [prefix-finding] [access_pc %lx] [actual_pc %lx] "
                    "[access_addr %lx] [width %u] [is_uaf %d]\n",
                    reference_pc, pc, addr, size, is_uaf ? 1 : 0);
        }
        return;
    }
    ProvPublishedFinding *slot = prov_fault_slot_for_publish(
        pf, quality, pc, addr, size);
    if (slot == NULL) {
        return;
    }

    ProvFindingRecord *rec = &slot->payload;
    rec->quality = quality;
    rec->is_uaf = is_uaf;
    rec->access_pc = reference_pc;
    rec->actual_pc = pc;
    provenance_memcheck_site(reference_pc, &rec->site);
    rec->access_addr = addr;
    rec->access_width = size;
    rec->object_id = obj_id;
    rec->generation = gen;
    rec->object_base = obj_base;
    rec->requested_size = obj_size;
    rec->tracked_offset = offset;
    rec->producer_pc = producer_pc;
    rec->producer_kind = producer_kind;
    rec->ea_base_reg = ea_base_reg;
    rec->ea_base_reg_val = ea_base_reg_val;
    rec->last_writer_pc = (ea_base_reg >= 0 && ea_base_reg < CPU_NB_REGS)
        ? provenance_get_reg_shadow(env)->last_writer_pc[ea_base_reg]
        : 0;

    /* A matching tagged promotion describes the same first access and keeps
     * its cursor boundary.  A direct first publication captures the current
     * first-unfilled indices. */
    if (slot == &pf->tagged &&
        atomic_load_acquire(&pf->fallback.ready) != 0) {
        slot->finding_query_idx = pf->fallback.finding_query_idx;
        slot->finding_expr_idx = pf->fallback.finding_expr_idx;
    } else {
        slot->finding_query_idx = (next_query != NULL && query_queue != NULL)
            ? (int64_t)(next_query - query_queue) : -1;
        slot->finding_expr_idx = (next_free_expr != NULL && pool != NULL)
            ? (int64_t)(next_free_expr - pool) : -1;
    }

    atomic_store_release(&slot->ready, 1);
}

MemcheckResult provenance_check_access(CPUArchState *env, target_ulong addr,
                                       target_ulong size, target_ulong pc,
                                       PtrTag ea_tag, int ea_base_reg,
                                       target_ulong ea_base_reg_val) {
    if (ea_tag.valid) {
        ProvenanceObject *obj = provenance_lookup_object(ea_tag.object_id,
                                                         ea_tag.generation);
        if (obj == NULL) {
            /* Identity absent: the tag is stale.  Invalidate the
             * authoritative register shadow (§7) and fall through to
             * UNKNOWN. */
            if (provenance_debug) {
                target_ulong writer = (ea_base_reg >= 0 &&
                                       ea_base_reg < CPU_NB_REGS)
                    ? provenance_get_reg_shadow(env)->last_writer_pc[ea_base_reg]
                    : 0;
                log_msg("[prov] [consistency] object not found [id %lu] [gen %u] [pc %lx] [ea_reg %d] [last_writer %lx] [producer_pc %lx] [kind %d]\n",
                        ea_tag.object_id, ea_tag.generation, pc, ea_base_reg,
                        writer, ea_tag.producer_pc, ea_tag.producer_kind);
            }
            if (ea_base_reg >= 0 && ea_base_reg < CPU_NB_REGS) {
                provenance_get_reg_shadow(env)->gpr[ea_base_reg].valid = false;
            }
            ea_tag.valid = false;
        } else if (ea_tag.concrete_value != ea_base_reg_val) {
            /* Value-consistency failure: tag's concrete_value doesn't match
             * the actual register value.  Invalidate the authoritative
             * register shadow (§7) and fall through to UNKNOWN. */
            if (provenance_debug) {
                target_ulong writer = (ea_base_reg >= 0 &&
                                       ea_base_reg < CPU_NB_REGS)
                    ? provenance_get_reg_shadow(env)->last_writer_pc[ea_base_reg]
                    : 0;
                log_msg("[prov] [consistency] tag value mismatch [tag %lx] [reg %lx] [pc %lx] [ea_reg %d] [last_writer %lx] [producer_pc %lx] [kind %d]\n",
                        ea_tag.concrete_value, ea_base_reg_val, pc, ea_base_reg,
                        writer, ea_tag.producer_pc, ea_tag.producer_kind);
            }
            if (ea_base_reg >= 0 && ea_base_reg < CPU_NB_REGS) {
                provenance_get_reg_shadow(env)->gpr[ea_base_reg].valid = false;
            }
            ea_tag.valid = false;
        } else {
            /* Tag is authoritative. */
            if (obj->state == PROV_OBJ_FREED) {
                /* UAF. */
                PendingProvenanceFault *pf = prov_pending_fault;
                prov_fault_fill(pf, env, pc, addr, size,
                                obj->object_id, obj->generation,
                                obj->base, obj->requested_size,
                                ea_tag.concrete_offset,
                                ea_tag.producer_pc, ea_tag.producer_kind,
                                ea_base_reg, ea_base_reg_val, true,
                                PROV_FINDING_TAGGED);
                if (provenance_debug) {
                    log_msg("[prov] [uaf] [pc %lx] [addr %lx] [width %u] [obj_id %lu] [gen %u] [base %lx] [size %lx] [offset %ld]\n",
                            pc, addr, size, obj->object_id, obj->generation,
                            obj->base, obj->requested_size, ea_tag.concrete_offset);
                }
                return MEMCHECK_HEAP_UAF;
            }

            /* LIVE: overflow-safe bounds check.  Compare the nonnegative
             * offset against the size in unsigned arithmetic so sizes
             * above INT64_MAX are not misclassified by a signed cast. */
            int64_t offset = ea_tag.concrete_offset;
            if (offset < 0 ||
                (uint64_t)offset > obj->requested_size) {
                /* OOB. */
                PendingProvenanceFault *pf = prov_pending_fault;
                prov_fault_fill(pf, env, pc, addr, size,
                                obj->object_id, obj->generation,
                                obj->base, obj->requested_size, offset,
                                ea_tag.producer_pc, ea_tag.producer_kind,
                                ea_base_reg, ea_base_reg_val, false,
                                PROV_FINDING_TAGGED);
                if (provenance_debug) {
                    log_msg("[prov] [oob] [pc %lx] [addr %lx] [width %u] [obj_id %lu] [gen %u] [base %lx] [size %lx] [offset %ld]\n",
                            pc, addr, size, obj->object_id, obj->generation,
                            obj->base, obj->requested_size, offset);
                }
                return MEMCHECK_HEAP_OOB;
            }

            /* Check: access_size > requested_size - offset (overflow-safe). */
            uint64_t remaining = (uint64_t)obj->requested_size - (uint64_t)offset;
            if ((uint64_t)size > remaining) {
                /* OOB: access extends past object end. */
                PendingProvenanceFault *pf = prov_pending_fault;
                prov_fault_fill(pf, env, pc, addr, size,
                                obj->object_id, obj->generation,
                                obj->base, obj->requested_size, offset,
                                ea_tag.producer_pc, ea_tag.producer_kind,
                                ea_base_reg, ea_base_reg_val, false,
                                PROV_FINDING_TAGGED);
                if (provenance_debug) {
                    log_msg("[prov] [oob] [pc %lx] [addr %lx] [width %u] [obj_id %lu] [gen %u] [base %lx] [size %lx] [offset %ld] [remaining %lu]\n",
                            pc, addr, size, obj->object_id, obj->generation,
                            obj->base, obj->requested_size, offset, remaining);
                }
                return MEMCHECK_HEAP_OOB;
            }

            /* In bounds — tag is authoritative, skip exact-bounds fallback. */
            return MEMCHECK_OK;
        }
    }

    /* UNKNOWN provenance: fall through to exact-bounds on LIVE objects.
     * Do NOT report UAF from numeric quarantine (cannot distinguish stale
     * pointer from valid pointer to reused/untracked allocation). */
    if (binradar_memcheck_enabled) {
        /* Check quarantine first (exact-bounds UAF from numeric match).
         * NOTE: we do NOT report UAF for UNKNOWN provenance per the spec.
         * The quarantine check is only for the exact-bounds OOB path. */
        SnapshotMemRegion *mr = mr_manager_heap_search_pub(addr);
        if (mr != NULL) {
            /* Exact-bounds OOB: access starts inside a known region but
             * extends past its end.  The search guarantees half-open
             * containment: mr->base <= addr < mr->base + mr->size, so
             * region_end - addr is well-defined (no wrap). */
            target_ulong region_end = mr->base + mr->size;
            /* Overflow-safe: if mr->base + mr->size wraps, the region is
             * invalid; treat as OK. */
            if (region_end >= mr->base) {
                /* size > region_end - addr ⇔ addr + size > region_end
                 * (overflow-safe: region_end - addr cannot wrap). */
                if (addr < region_end &&
                    (uint64_t)size > (uint64_t)(region_end - addr)) {
                    /* Record non-fatal finding. */
                    PendingProvenanceFault *pf = prov_pending_fault;
                    prov_fault_fill(pf, env, pc, addr, size,
                                    0, 0, mr->base, mr->size,
                                    (int64_t)(addr - mr->base),
                                    0, PROV_PRODUCER_NONE,
                                    ea_base_reg, ea_base_reg_val, false,
                                    PROV_FINDING_FALLBACK);
                    if (provenance_debug) {
                        log_msg("[prov] [oob-exact] [pc %lx] [addr %lx] [width %u] [base %lx] [size %lx]\n",
                                pc, addr, size, mr->base, mr->size);
                    }
                    return MEMCHECK_HEAP_OOB;
                }
            }
        }
    }

    return MEMCHECK_OK;
}

/* Snapshot the preferred committed finding.  Each slot is immutable after
 * its release publication, so an acquire followed by a plain structure copy
 * is sufficient.  A killed, half-written tagged promotion has ready == 0 and
 * falls back to the previously committed UNKNOWN record. */
bool provenance_snapshot_pending_finding(ProvPublishedFinding *out) {
    if (prov_pending_fault == NULL || out == NULL) {
        return false;
    }
    if (atomic_load_acquire(&prov_pending_fault->tagged.ready) != 0) {
        *out = prov_pending_fault->tagged;
        return true;
    }
    if (atomic_load_acquire(&prov_pending_fault->fallback.ready) != 0) {
        *out = prov_pending_fault->fallback;
        return true;
    }
    return false;
}

void provenance_clear_pending_fault(void) {
    if (prov_pending_fault != NULL) {
        memset(prov_pending_fault, 0, sizeof(*prov_pending_fault));
    }
}

/* ---- Deferred crash finalization ---- */

bool provenance_finalize_fault(CPUArchState *env) {
    ProvPublishedFinding finding;
    (void)env;
    return provenance_snapshot_pending_finding(&finding);
}

static const char *prov_fault_reason_for(const ProvFindingRecord *finding) {
    return finding->is_uaf
        ? "memcheck: heap-use-after-free (provenance)"
        : "memcheck: heap-buffer-overflow (provenance)";
}

const char *provenance_fault_reason(void) {
    ProvPublishedFinding finding;
    return provenance_snapshot_pending_finding(&finding)
        ? prov_fault_reason_for(&finding.payload) : NULL;
}

/* Emit the structured finding line exactly once (§8: preserve both the
 * pending provenance event and any real crash record; the real crash
 * selects the verdict).  Returns true if a finding was emitted. */
bool provenance_report_pending_finding(void) {
    ProvPublishedFinding finding;
    if (prov_pending_fault == NULL ||
        !provenance_snapshot_pending_finding(&finding)) {
        return false;
    }
    if (prov_pending_fault->reported) {
        return true;
    }

    const ProvFindingRecord *f = &finding.payload;
    log_msg("[prov] [finalize] [finding] [reason %s] [access_pc %lx] [actual_pc %lx] [access_addr %lx] [width %u] [obj_id %lu] [gen %u] [obj_base %lx] [size %lx] [offset %ld] [producer_pc %lx] [kind %d] [last_writer %lx] [is_uaf %d] [ea_reg %d] [query_cursor %ld] [expr_cursor %ld]\n",
            prov_fault_reason_for(f), f->access_pc, f->actual_pc, f->access_addr,
            f->access_width, f->object_id, f->generation,
            f->object_base, f->requested_size, f->tracked_offset,
            f->producer_pc, f->producer_kind, f->last_writer_pc,
            f->is_uaf, f->ea_base_reg, finding.finding_query_idx,
            finding.finding_expr_idx);
    prov_pending_fault->reported = true;
    return true;
}

/* ---- snapshot_modify_memory hooks ---- */

void provenance_on_modify_reg(CPUArchState *env, int reg_idx) {
    provenance_invalidate_reg(env, reg_idx, 0);
}

void provenance_on_modify_mem(target_ulong addr, target_ulong size) {
    provenance_mem_invalidate(addr, size);
}

/* ---- Debug logging ---- */

void provenance_log_tag(const char *ctx, int reg_idx, PtrTag tag) {
    if (!provenance_debug) return;
    if (tag.valid) {
        log_msg("[prov] [%s] [reg %d] [obj_id %lu] [gen %u] [offset %ld] [value %lx] [producer_pc %lx] [kind %d]\n",
                ctx, reg_idx, tag.object_id, tag.generation,
                tag.concrete_offset, tag.concrete_value,
                tag.producer_pc, tag.producer_kind);
    } else {
        log_msg("[prov] [%s] [reg %d] UNKNOWN\n", ctx, reg_idx);
    }
}
/* C API used by libc-model bodies (tcg/symbolic/symbolic.c): the caller
 * names the register that holds the pointer, so no EA scratch is needed.
 * A single register source is always a sound base (no scale/disp). */
void provenance_model_check_access(CPUArchState *env, target_ulong addr,
                                   target_ulong size, target_ulong pc,
                                   int reg) {
    if (!binradar_memcheck_enabled) return;
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    PtrTag tag = {0};
    target_ulong reg_val = 0;
    if (reg >= 0 && reg < CPU_NB_REGS) {
        tag = shadow->gpr[reg];
        reg_val = env->regs[reg];
        if (!tag.valid) {
            tag = (PtrTag){0};
        }
    }
    provenance_check_access(env, addr, size, pc, tag, reg, reg_val);
}
