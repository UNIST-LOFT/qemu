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
#include "tcg/symbolic/symbolic-instrumentation.h"
#include "exec/helper-head.h"
/* Declare helper prototypes for the DEF_HELPER-declared provenance
 * helpers in target/i386/helper.h.  We can't include exec/helper-proto.h
 * here because it pulls in target-specific helper.h.  Instead, declare
 * the prototypes manually to satisfy -Werror=missing-prototypes. */
void helper_prov_invalidate_reg(CPUArchState *env, uint32_t reg_idx,
                                target_ulong pc);
void helper_prov_mov_reg(CPUArchState *env, uint32_t dst_idx, uint32_t src_idx,
                         target_ulong src_val, target_ulong dst_val,
                         target_ulong pc);
void helper_prov_lea_imm(CPUArchState *env, uint32_t dst_idx,
                         uint32_t base_idx, target_ulong disp,
                         target_ulong dst_val, target_ulong base_val);
void helper_prov_addsub_imm(CPUArchState *env, uint32_t reg_idx,
                            target_ulong delta, target_ulong pre_val,
                            target_ulong post_val, target_ulong pc);
void helper_prov_clobber_caller_saved(CPUArchState *env);
void helper_prov_xchg_reg(CPUArchState *env, uint32_t dst_idx,
                          uint32_t src_idx);
void helper_prov_on_load(CPUArchState *env, uint32_t dst_idx,
                         target_ulong addr, target_ulong size,
                         target_ulong pc);
void helper_prov_on_store(CPUArchState *env, uint32_t src_idx,
                          target_ulong addr, target_ulong size);
void helper_prov_set_ea(CPUArchState *env, uint32_t base_reg,
                        uint32_t index_reg, uint32_t scale,
                        target_ulong disp);
void helper_prov_set_pc(CPUArchState *env, target_ulong pc);
void helper_prov_check_access(CPUArchState *env, target_ulong addr,
                              target_ulong size, target_ulong pc);
void helper_prov_addsub_reg(CPUArchState *env, uint32_t dst_idx,
                            uint32_t src_idx, target_ulong pc,
                            target_ulong dst_val, target_ulong src_val);

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

/* Solver pool cursors (shared/fork-inherited): captured at finding time
 * so the timeout path can publish final query/expr cursors.  The opaque
 * typedefs come from snapshot.h. */
extern Query *next_query;
extern Expr *next_free_expr;

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

/* Table synchronization (glib hash tables in process-global memory):
 * - Forkserver model: the tables live in the parent's address space before
 *   fork; each child gets a private COW copy, so there is no cross-process
 *   sharing and no locking is needed across children.
 * - linux-user TCG is single-threaded by construction: qemu_tcg_configure()
 *   (the only writer of mttcg_enabled) is softmmu-only (vl.c), so MTTCG is
 *   never enabled in linux-user mode.  Guest threads (clone) are serialized
 *   through start_exclusive()/end_exclusive() in the main thread, so all
 *   provenance helpers run on one host thread.  GLib hash tables therefore
 *   need no lock; this is an enforced invariant, not an assumption.
 * - If MTTCG is ever enabled for linux-user, every access to
 *   prov_object_table / prov_live_by_base / prov_mem_shadow /
 *   prov_reg_shadows and to the shared pending fault must be wrapped in a
 *   QemuMutex before that happens.  The per-CPU PtrRegShadow entries are
 *   keyed by env*, so they are naturally independent per vCPU. */
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
 *   dst tagged, src untagged: dst = dst ± src → fold ±src_val.
 *   dst untagged, src tagged, ADD: dst = src + dst → delta = dst − src. */
void provenance_addsub_reg(CPUArchState *env, int dst_idx, int src_idx,
                           int is_sub, target_ulong pc,
                           target_ulong dst_val, target_ulong src_val) {
    if (dst_idx < 0 || dst_idx >= CPU_NB_REGS) return;
    if (src_idx < 0 || src_idx >= CPU_NB_REGS) return;
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    PtrTag dst_tag = shadow->gpr[dst_idx];
    PtrTag src_tag = shadow->gpr[src_idx];
    if (dst_tag.valid && !src_tag.valid) {
        int64_t delta = is_sub ? -(int64_t)src_val : (int64_t)src_val;
        int64_t expect;
        if (__builtin_add_overflow((int64_t)dst_tag.concrete_value, delta,
                                   &expect) ||
            expect != (int64_t)dst_val) {
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
        /* ADD with dst the untagged offset and src the pointer:
         * result = src + dst; delta = new_dst − src_val. */
        int64_t delta;
        if (__builtin_sub_overflow((int64_t)dst_val, (int64_t)src_val,
                                   &delta)) {
            shadow->gpr[dst_idx].valid = false;
            shadow->last_writer_pc[dst_idx] = pc;
            return;
        }
        if ((int64_t)src_tag.concrete_value != (int64_t)src_val) {
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

/* Fill the common fields of a pending provenance fault.  Captures the
 * last writer PC of the EA base register (shadow last_writer_pc) for
 * observability; 0 when the register is unknown. */
static void prov_fault_fill(PendingProvenanceFault *pf, CPUArchState *env,
                            target_ulong pc, target_ulong addr, uint32_t size,
                            uint64_t obj_id, uint32_t gen,
                            target_ulong obj_base, target_ulong obj_size,
                            int64_t offset, target_ulong producer_pc,
                            PtrProducerKind producer_kind, int ea_base_reg,
                            target_ulong ea_base_reg_val, bool is_uaf) {
    pf->detected = true;
    pf->is_uaf = is_uaf;
    pf->access_pc = pc;
    pf->access_addr = addr;
    pf->access_width = size;
    pf->object_id = obj_id;
    pf->generation = gen;
    pf->object_base = obj_base;
    pf->requested_size = obj_size;
    pf->tracked_offset = offset;
    pf->producer_pc = producer_pc;
    pf->producer_kind = producer_kind;
    pf->ea_base_reg = ea_base_reg;
    pf->ea_base_reg_val = ea_base_reg_val;
    pf->last_writer_pc = (ea_base_reg >= 0 && ea_base_reg < CPU_NB_REGS)
        ? provenance_get_reg_shadow(env)->last_writer_pc[ea_base_reg]
        : 0;
    /* Final solver cursors: captured while the child is alive so the
     * timeout path can publish them after SIGKILL (§P1). */
    pf->next_query = (uintptr_t)next_query;
    pf->next_free_expr = (uintptr_t)next_free_expr;
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
                if (pf && !pf->detected) {
                    prov_fault_fill(pf, env, pc, addr, size,
                                    obj->object_id, obj->generation,
                                    obj->base, obj->requested_size,
                                    ea_tag.concrete_offset,
                                    ea_tag.producer_pc, ea_tag.producer_kind,
                                    ea_base_reg, ea_base_reg_val, true);
                }
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
                if (pf && !pf->detected) {
                    prov_fault_fill(pf, env, pc, addr, size,
                                    obj->object_id, obj->generation,
                                    obj->base, obj->requested_size, offset,
                                    ea_tag.producer_pc, ea_tag.producer_kind,
                                    ea_base_reg, ea_base_reg_val, false);
                }
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
                if (pf && !pf->detected) {
                    prov_fault_fill(pf, env, pc, addr, size,
                                    obj->object_id, obj->generation,
                                    obj->base, obj->requested_size, offset,
                                    ea_tag.producer_pc, ea_tag.producer_kind,
                                    ea_base_reg, ea_base_reg_val, false);
                }
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
                    if (pf && !pf->detected) {
                        prov_fault_fill(pf, env, pc, addr, size,
                                        0, 0, mr->base, mr->size,
                                        (int64_t)(addr - mr->base),
                                        0, PROV_PRODUCER_NONE,
                                        ea_base_reg, ea_base_reg_val, false);
                    }
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

/* ---- Pending fault ---- */

PendingProvenanceFault *provenance_get_pending_fault(void) {
    return prov_pending_fault;
}

void provenance_clear_pending_fault(void) {
    if (prov_pending_fault) {
        memset(prov_pending_fault, 0, sizeof(*prov_pending_fault));
    }
}

/* ---- Deferred crash finalization ---- */

bool provenance_finalize_fault(CPUArchState *env) {
    (void)env;
    return prov_pending_fault && prov_pending_fault->detected;
}

const char *provenance_fault_reason(void) {
    if (!prov_pending_fault || !prov_pending_fault->detected) return NULL;
    return prov_pending_fault->is_uaf
        ? "memcheck: heap-use-after-free (provenance)"
        : "memcheck: heap-buffer-overflow (provenance)";
}

/* Emit the structured finding line exactly once (§8: preserve both the
 * pending provenance event and any real crash record; the real crash
 * selects the verdict).  Returns true if a finding was emitted. */
bool provenance_report_pending_finding(void) {
    if (!prov_pending_fault || !prov_pending_fault->detected) return false;
    if (prov_pending_fault->reported) return true;
    PendingProvenanceFault *fault = prov_pending_fault;
    const char *pf_reason = provenance_fault_reason();
    log_msg("[prov] [finalize] [finding] [reason %s] [access_pc %lx] [access_addr %lx] [width %u] [obj_id %lu] [gen %u] [obj_base %lx] [size %lx] [offset %ld] [producer_pc %lx] [kind %d] [last_writer %lx] [is_uaf %d] [ea_reg %d]\n",
            pf_reason ? pf_reason : "?", fault->access_pc, fault->access_addr,
            fault->access_width, fault->object_id, fault->generation,
            fault->object_base, fault->requested_size, fault->tracked_offset,
            fault->producer_pc, fault->producer_kind, fault->last_writer_pc,
            fault->is_uaf, fault->ea_base_reg);
    fault->reported = true;
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
/* ---- TCG helper functions (called from translated code) ---- */
/* These use the helper_ prefix expected by DEF_HELPER.  The DEF_HELPER
 * system generates gen_helper_* wrappers that handle TCG plumbing. */

void helper_prov_invalidate_reg(CPUArchState *env, uint32_t reg_idx,
                                target_ulong pc) {
    provenance_invalidate_reg(env, reg_idx, pc);
}

void helper_prov_mov_reg(CPUArchState *env, uint32_t dst_idx,
                         uint32_t src_idx, target_ulong src_val,
                         target_ulong dst_val, target_ulong pc) {
    provenance_propagate_mov(env, dst_idx, src_idx, pc, src_val, dst_val);
}

void helper_prov_lea_imm(CPUArchState *env, uint32_t dst_idx,
                         uint32_t base_idx, target_ulong disp,
                         target_ulong dst_val, target_ulong base_val) {
    /* The exact instruction PC was recorded in the per-CPU scratch by
     * helper_prov_set_pc (see gen_prov_lea_imm). */
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    target_ulong pc = shadow->cur_pc;
    provenance_lea_imm(env, dst_idx, base_idx,
                       (int64_t)(int32_t)disp, pc, dst_val, base_val);
}

void helper_prov_addsub_imm(CPUArchState *env, uint32_t reg_idx,
                            target_ulong delta, target_ulong pre_val,
                            target_ulong post_val, target_ulong pc) {
    provenance_addsub_imm(env, reg_idx, (int64_t)(int64_t)delta, pc,
                          pre_val, post_val);
}

void helper_prov_addsub_reg(CPUArchState *env, uint32_t dst_idx,
                            uint32_t src_idx, target_ulong pc,
                            target_ulong dst_val, target_ulong src_val) {
    int is_sub = (dst_idx >> 16) & 1;
    provenance_addsub_reg(env, dst_idx & 0xffff, src_idx, is_sub, pc,
                          dst_val, src_val);
}

void helper_prov_clobber_caller_saved(CPUArchState *env) {
    provenance_clobber_caller_saved(env);
}

void helper_prov_xchg_reg(CPUArchState *env, uint32_t dst_idx,
                          uint32_t src_idx) {
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    if (dst_idx >= CPU_NB_REGS || src_idx >= CPU_NB_REGS) return;
    PtrTag tmp = shadow->gpr[dst_idx];
    shadow->gpr[dst_idx] = shadow->gpr[src_idx];
    shadow->gpr[src_idx] = tmp;
    target_ulong tmp_pc = shadow->last_writer_pc[dst_idx];
    shadow->last_writer_pc[dst_idx] = shadow->last_writer_pc[src_idx];
    shadow->last_writer_pc[src_idx] = tmp_pc;
}

void helper_prov_on_load(CPUArchState *env, uint32_t dst_idx,
                         target_ulong addr, target_ulong size,
                         target_ulong pc) {
    if (size == sizeof(target_ulong)) {
        PtrTag mem_tag = provenance_mem_load_tag(addr);
        if (mem_tag.valid) {
            target_ulong actual_val = 0;
            void *h = g2h(addr);
            memcpy(&actual_val, h, sizeof(target_ulong));
            if (mem_tag.concrete_value == actual_val) {
                mem_tag.producer_pc = pc;
                mem_tag.producer_kind = PROV_PRODUCER_LOAD;
                provenance_set_reg_tag(env, dst_idx, mem_tag);
                return;
            }
            /* Value mismatch: the slot's bytes no longer match the saved
             * tag.  Remove the stale entry so a later coincidental byte
             * match cannot resurrect it (§5). */
            provenance_mem_invalidate(addr, sizeof(target_ulong));
        }
    }
    provenance_invalidate_reg(env, dst_idx, pc);
}

void helper_prov_on_store(CPUArchState *env, uint32_t src_idx,
                          target_ulong addr, target_ulong size) {
    if (size == sizeof(target_ulong) &&
        (addr & (sizeof(target_ulong) - 1)) == 0) {
        PtrTag tag = provenance_get_reg_tag(env, src_idx);
        if (tag.valid) {
            target_ulong stored_val = env->regs[src_idx];
            if (tag.concrete_value == stored_val) {
                provenance_mem_store_tag(addr, tag);
                return;
            }
        }
        provenance_mem_invalidate(addr, size);
    } else {
        provenance_mem_invalidate(addr, size);
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

void helper_prov_set_pc(CPUArchState *env, target_ulong pc) {
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    shadow->cur_pc = pc;
}

void helper_prov_set_ea(CPUArchState *env, uint32_t base_reg,
                        uint32_t index_reg, uint32_t scale,
                        target_ulong disp) {
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    shadow->ea_meta.base_reg = (int32_t)base_reg;
    shadow->ea_meta.index_reg = (int32_t)index_reg;
    shadow->ea_meta.scale = (int32_t)scale;
    shadow->ea_meta.disp = (target_long)disp;
    /* Snapshot the pre-access concrete values and tags.  The check runs
     * AFTER the guest load/store; a load whose destination overwrites its
     * own EA base/index register must not make the check observe the
     * loaded value/tag instead of the address-producing state (§6). */
    if (base_reg < CPU_NB_REGS) {
        shadow->ea_meta.base_val = env->regs[base_reg];
        shadow->ea_meta.base_tag = shadow->gpr[base_reg];
    } else {
        shadow->ea_meta.base_val = 0;
        shadow->ea_meta.base_tag = (PtrTag){0};
    }
    if (index_reg < CPU_NB_REGS) {
        shadow->ea_meta.index_val = env->regs[index_reg];
        shadow->ea_meta.index_tag = shadow->gpr[index_reg];
    } else {
        shadow->ea_meta.index_val = 0;
        shadow->ea_meta.index_tag = (PtrTag){0};
    }
    shadow->ea_meta.valid = true;
}

void helper_prov_check_access(CPUArchState *env, target_ulong addr,
                              target_ulong size, target_ulong pc) {
    if (!binradar_memcheck_enabled) return;
    if (symbolic_start_code > 0 &&
        (pc < symbolic_start_code || pc >= symbolic_end_code)) {
        return;
    }
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    int ea_src_reg = -1;
    target_ulong ea_src_val = 0;
    /* Consume the EA metadata: copy into locals, then clear so a stale
     * record can never be misread by a later instruction. */
    bool have_ea = shadow->ea_meta.valid;
    int base_reg = shadow->ea_meta.base_reg;
    int index_reg = shadow->ea_meta.index_reg;
    int scale = shadow->ea_meta.scale;
    target_long disp = shadow->ea_meta.disp;
    /* Pre-access snapshots taken by helper_prov_set_ea (before the guest
     * load/store), so a self-overwriting load cannot corrupt them. */
    PtrTag base_tag = shadow->ea_meta.base_tag;
    PtrTag index_tag = shadow->ea_meta.index_tag;
    target_ulong base_val = shadow->ea_meta.base_val;
    target_ulong index_val = shadow->ea_meta.index_val;
    shadow->ea_meta.valid = false;
    if (have_ea) {
        /* Semantic EA propagation (§6).  Only these first-version forms
         * carry identity:
         *   [tagged_base + disp]: propagate base identity, offset += disp
         *     (translation-time disp, value-consistency checked).
         *   [tagged_index*1 + disp] with no base: propagate the index
         *     identity, offset += disp.
         * Everything else — two tagged inputs, scale != 1 on the tagged
         * operand, truncating address modes, unmodeled segment bases —
         * is UNKNOWN (exact-bounds fallback only).  No numeric delta
         * reconstruction is performed. */
        if (base_reg >= 0 && base_reg < CPU_NB_REGS) {
            if (index_reg < 0 && base_tag.valid) {
                /* [base + disp]: the access address must equal
                 * base_val + disp (semantic, translation-time disp). */
                target_ulong expect = (target_ulong)((int64_t)base_val + disp);
                if (expect == addr) {
                    int64_t new_offset;
                    if (__builtin_add_overflow(base_tag.concrete_offset,
                                               (int64_t)disp, &new_offset)) {
                        base_tag.valid = false;  /* overflow → UNKNOWN */
                    } else {
                        base_tag.concrete_offset = new_offset;
                    }
                } else {
                    base_tag.valid = false;
                }
                ea_src_reg = base_reg;
                ea_src_val = base_val;
                provenance_check_access(env, addr, size, pc, base_tag,
                                        ea_src_reg, ea_src_val);
                return;
            }
            /* base + index: two-register form.  If BOTH carry valid tags
             * there is no sound merge rule — UNKNOWN.  If only the base
             * is tagged, the index is a pure integer offset; the access
             * address must equal base_val + index_val*scale + disp
             * (semantic, no numeric reconstruction). */
            if (index_reg >= 0 && base_tag.valid) {
                if (index_tag.valid) {
                    /* Two tagged inputs: no sound merge (§6). */
                    provenance_check_access(env, addr, size, pc,
                                            (PtrTag){0}, -1, 0);
                    return;
                }
                /* Untagged index: the address must match the semantic
                 * decomposition exactly (scale is the SIB shift 0..3).
                 * Only then fold the runtime delta addr - base_val into
                 * the tracked offset, with checked arithmetic. */
                int64_t idx_part = (int64_t)index_val << scale;
                target_ulong expect = (target_ulong)((int64_t)base_val +
                                                     idx_part + disp);
                if (expect == addr) {
                    int64_t delta;
                    int64_t new_offset;
                    if (__builtin_sub_overflow((int64_t)addr,
                                               (int64_t)base_val, &delta) ||
                        __builtin_add_overflow(base_tag.concrete_offset,
                                               delta, &new_offset)) {
                        base_tag.valid = false;  /* overflow → UNKNOWN */
                    } else {
                        base_tag.concrete_offset = new_offset;
                    }
                } else {
                    base_tag.valid = false;
                }
                ea_src_reg = base_reg;
                ea_src_val = base_val;
                provenance_check_access(env, addr, size, pc, base_tag,
                                        ea_src_reg, ea_src_val);
                return;
            }
        }
        if (index_reg >= 0 && index_reg < CPU_NB_REGS) {
            /* Index carries the provenance and the base is untagged or
             * absent.  Only scale 1 is sound (§6): the address must
             * equal index_val + disp. */
            if (index_tag.valid && scale == 0) {
                target_ulong expect = (target_ulong)((int64_t)index_val + disp);
                if (expect == addr) {
                    int64_t new_offset;
                    if (__builtin_add_overflow(index_tag.concrete_offset,
                                               (int64_t)disp, &new_offset)) {
                        index_tag.valid = false;
                    } else {
                        index_tag.concrete_offset = new_offset;
                    }
                } else {
                    index_tag.valid = false;
                }
                ea_src_reg = index_reg;
                ea_src_val = index_val;
                provenance_check_access(env, addr, size, pc, index_tag,
                                        ea_src_reg, ea_src_val);
                return;
            }
        }
        /* All unsupported forms → UNKNOWN provenance (exact-bounds
         * fallback only). */
        provenance_check_access(env, addr, size, pc, (PtrTag){0},
                                ea_src_reg, ea_src_val);
        return;
    }
    provenance_check_access(env, addr, size, pc, (PtrTag){0}, -1, 0);
}