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
extern uint64_t symbolic_start_code;
extern uint64_t symbolic_end_code;

/* Per-run pending fault.  Stored inside SharedTraceData (the shared mmap)
 * so the parent can read it after waitpid even when the child was killed
 * or hit the forkserver timeout; set via provenance_set_shared_fault_ptr
 * from snapshot_init right after the shared mapping is created. */
static PendingProvenanceFault *prov_pending_fault = NULL;

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
    return fallback->access_pc == pc &&
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
    ProvPublishedFinding *slot = prov_fault_slot_for_publish(
        pf, quality, pc, addr, size);
    if (slot == NULL) {
        return;
    }

    ProvFindingRecord *rec = &slot->payload;
    rec->quality = quality;
    rec->is_uaf = is_uaf;
    rec->access_pc = pc;
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
    if (binradar_memcheck_enabled && symbolic_start_code > 0 &&
        pc >= symbolic_start_code && pc < symbolic_end_code) {
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
    log_msg("[prov] [finalize] [finding] [reason %s] [access_pc %lx] [access_addr %lx] [width %u] [obj_id %lu] [gen %u] [obj_base %lx] [size %lx] [offset %ld] [producer_pc %lx] [kind %d] [last_writer %lx] [is_uaf %d] [ea_reg %d] [query_cursor %ld] [expr_cursor %ld]\n",
            prov_fault_reason_for(f), f->access_pc, f->access_addr,
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
