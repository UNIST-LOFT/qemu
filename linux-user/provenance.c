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
                         target_ulong src_val, target_ulong dst_val);
void helper_prov_lea_imm(CPUArchState *env, uint32_t dst_idx,
                         uint32_t base_idx, target_ulong disp,
                         target_ulong dst_val, target_ulong base_val);
void helper_prov_addsub_imm(CPUArchState *env, uint32_t reg_idx,
                            target_ulong delta, target_ulong pre_val,
                            target_ulong post_val);
void helper_prov_clobber_caller_saved(CPUArchState *env);
void helper_prov_on_load(CPUArchState *env, uint32_t dst_idx,
                         target_ulong addr, target_ulong size);
void helper_prov_on_store(CPUArchState *env, uint32_t src_idx,
                          target_ulong addr, target_ulong size);
void helper_prov_check_access(CPUArchState *env, target_ulong addr,
                              target_ulong size, target_ulong pc,
                              uint32_t base_reg, uint32_t index_reg);
void helper_prov_addsub_reg(CPUArchState *env, uint32_t dst_idx,
                            uint32_t src_idx, target_ulong pc,
                            target_ulong dst_val, target_ulong src_val);

int provenance_debug = 0;

/* ---- Allocation object table ---- */

/* Object identity counter.  Monotonic; never reused. */
static uint64_t prov_next_object_id = 1;

/* Persistent table: {object_id, generation} → ProvenanceObject.
 * Objects are never erased (even when FREED) so stale tags can still
 * resolve to a FREED object for UAF reporting. */
typedef struct {
    uint64_t object_id;
    uint32_t generation;
} ObjKey;

static GHashTable *prov_object_table = NULL;   /* ObjKey → ProvenanceObject* */
static GHashTable *prov_live_by_base = NULL;   /* base → ObjKey* (LIVE only) */

/* Pending allocator operation (one at a time, single-threaded guest). */
static ProvenancePending prov_pending = {0};

/* Per-run pending fault (lives in shared output state area, but
 * for simplicity we keep it process-local since fork children exit
 * before the parent reads shared_trace_data). */
static PendingProvenanceFault prov_pending_fault = {0};

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

void provenance_init(void) {
    prov_ensure_tables();
    memset(&prov_pending, 0, sizeof(prov_pending));
    memset(&prov_pending_fault, 0, sizeof(prov_pending_fault));
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

/* ---- Pending allocator operations ---- */

void provenance_set_pending(ProvenancePendingKind kind, target_ulong call_pc,
                            target_ulong arg_size, target_ulong arg_ptr) {
    prov_ensure_tables();
    prov_pending.valid = true;
    prov_pending.kind = kind;
    prov_pending.call_pc = call_pc;
    prov_pending.arg_size = arg_size;
    prov_pending.arg_ptr = arg_ptr;
    prov_pending.old_object_id = 0;
    prov_pending.old_generation = 0;
}

ProvenancePending provenance_get_pending(target_ulong call_pc) {
    if (prov_pending.valid && prov_pending.call_pc == call_pc) {
        return prov_pending;
    }
    ProvenancePending empty = {0};
    return empty;
}

void provenance_clear_pending(void) {
    memset(&prov_pending, 0, sizeof(prov_pending));
}

/* ---- Register tag operations ---- */

void provenance_invalidate_reg(CPUArchState *env, int reg_idx,
                               target_ulong pc) {
    if (reg_idx < 0 || reg_idx >= CPU_NB_REGS) return;
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    shadow->gpr[reg_idx].valid = false;
}

void provenance_set_reg_tag(CPUArchState *env, int reg_idx, PtrTag tag) {
    if (reg_idx < 0 || reg_idx >= CPU_NB_REGS) return;
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    shadow->gpr[reg_idx] = tag;
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
    /* Checked offset arithmetic: offset + disp. */
    int64_t new_offset = base_tag.concrete_offset + disp;
    /* Check for int64_t overflow. */
    if ((disp > 0 && new_offset < base_tag.concrete_offset) ||
        (disp < 0 && new_offset > base_tag.concrete_offset)) {
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
    int64_t new_offset = tag.concrete_offset + delta;
    if ((delta > 0 && new_offset < tag.concrete_offset) ||
        (delta < 0 && new_offset > tag.concrete_offset)) {
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
        if ((int64_t)dst_tag.concrete_value + delta != (int64_t)dst_val) {
            shadow->gpr[dst_idx].valid = false;
            shadow->last_writer_pc[dst_idx] = pc;
            return;
        }
        int64_t new_offset = dst_tag.concrete_offset + delta;
        if ((delta > 0 && new_offset < dst_tag.concrete_offset) ||
            (delta < 0 && new_offset > dst_tag.concrete_offset)) {
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
        int64_t delta = (int64_t)dst_val - (int64_t)src_val;
        if ((int64_t)src_tag.concrete_value != (int64_t)src_val) {
            shadow->gpr[dst_idx].valid = false;
            shadow->last_writer_pc[dst_idx] = pc;
            return;
        }
        int64_t new_offset = src_tag.concrete_offset + delta;
        if ((delta > 0 && new_offset < src_tag.concrete_offset) ||
            (delta < 0 && new_offset > src_tag.concrete_offset)) {
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
    /* Align to pointer size. */
    target_ulong aligned = addr & ~(target_ulong)(sizeof(target_ulong) - 1);
    if (tag.valid) {
        PtrMemEntry *entry = g_new(PtrMemEntry, 1);
        entry->addr = aligned;
        entry->tag = tag;
        g_hash_table_replace(prov_mem_shadow,
                             GINT_TO_POINTER((uintptr_t)aligned), entry);
    } else {
        g_hash_table_remove(prov_mem_shadow,
                            GINT_TO_POINTER((uintptr_t)aligned));
    }
}

PtrTag provenance_mem_load_tag(target_ulong addr) {
    if (prov_mem_shadow == NULL) {
        PtrTag unknown = {0};
        return unknown;
    }
    target_ulong aligned = addr & ~(target_ulong)(sizeof(target_ulong) - 1);
    PtrMemEntry *entry = g_hash_table_lookup(prov_mem_shadow,
                                             GINT_TO_POINTER((uintptr_t)aligned));
    if (entry == NULL) {
        PtrTag unknown = {0};
        return unknown;
    }
    /* Value-consistency: the saved concrete value must match the bytes
     * actually at this address.  The caller must verify this. */
    return entry->tag;
}

void provenance_mem_invalidate(target_ulong addr, target_ulong size) {
    if (prov_mem_shadow == NULL) return;
    /* Invalidate all aligned slots overlapping [addr, addr+size). */
    target_ulong start = addr & ~(target_ulong)(sizeof(target_ulong) - 1);
    target_ulong end = (addr + size + sizeof(target_ulong) - 1) &
                       ~(target_ulong)(sizeof(target_ulong) - 1);
    for (target_ulong a = start; a < end; a += sizeof(target_ulong)) {
        g_hash_table_remove(prov_mem_shadow,
                            GINT_TO_POINTER((uintptr_t)a));
    }
}

/* ---- Access checking ---- */

MemcheckResult provenance_check_access(CPUArchState *env, target_ulong addr,
                                       target_ulong size, target_ulong pc,
                                       PtrTag ea_tag, int ea_base_reg,
                                       target_ulong ea_base_reg_val) {
    if (ea_tag.valid) {
        ProvenanceObject *obj = provenance_lookup_object(ea_tag.object_id,
                                                         ea_tag.generation);
        if (obj == NULL) {
            /* Identity absent: invalidate tag, fall through to UNKNOWN. */
            if (provenance_debug) {
                log_msg("[prov] [consistency] object not found [id %lu] [gen %u] [pc %lx]\n",
                        ea_tag.object_id, ea_tag.generation, pc);
            }
            ea_tag.valid = false;
        } else if (ea_tag.concrete_value != ea_base_reg_val) {
            /* Value-consistency failure: tag's concrete_value doesn't match
             * the actual register value.  Invalidate, fall through. */
            if (provenance_debug) {
                log_msg("[prov] [consistency] tag value mismatch [tag %lx] [reg %lx] [pc %lx]\n",
                        ea_tag.concrete_value, ea_base_reg_val, pc);
            }
            ea_tag.valid = false;
        } else {
            /* Tag is authoritative. */
            if (obj->state == PROV_OBJ_FREED) {
                /* UAF. */
                if (!prov_pending_fault.detected) {
                    prov_pending_fault.detected = true;
                    prov_pending_fault.is_uaf = true;
                    prov_pending_fault.access_pc = pc;
                    prov_pending_fault.access_addr = addr;
                    prov_pending_fault.access_width = size;
                    prov_pending_fault.object_id = obj->object_id;
                    prov_pending_fault.generation = obj->generation;
                    prov_pending_fault.object_base = obj->base;
                    prov_pending_fault.requested_size = obj->requested_size;
                    prov_pending_fault.tracked_offset = ea_tag.concrete_offset;
                    prov_pending_fault.producer_pc = ea_tag.producer_pc;
                    prov_pending_fault.producer_kind = ea_tag.producer_kind;
                    prov_pending_fault.ea_base_reg = ea_base_reg;
                    prov_pending_fault.ea_base_reg_val = ea_base_reg_val;
                }
                if (provenance_debug) {
                    log_msg("[prov] [uaf] [pc %lx] [addr %lx] [width %u] [obj_id %lu] [gen %u] [base %lx] [size %lx] [offset %ld]\n",
                            pc, addr, size, obj->object_id, obj->generation,
                            obj->base, obj->requested_size, ea_tag.concrete_offset);
                }
                return MEMCHECK_HEAP_UAF;
            }

            /* LIVE: overflow-safe bounds check. */
            int64_t offset = ea_tag.concrete_offset;
            if (offset < 0 || offset > (int64_t)obj->requested_size) {
                /* OOB. */
                if (!prov_pending_fault.detected) {
                    prov_pending_fault.detected = true;
                    prov_pending_fault.is_uaf = false;
                    prov_pending_fault.access_pc = pc;
                    prov_pending_fault.access_addr = addr;
                    prov_pending_fault.access_width = size;
                    prov_pending_fault.object_id = obj->object_id;
                    prov_pending_fault.generation = obj->generation;
                    prov_pending_fault.object_base = obj->base;
                    prov_pending_fault.requested_size = obj->requested_size;
                    prov_pending_fault.tracked_offset = offset;
                    prov_pending_fault.producer_pc = ea_tag.producer_pc;
                    prov_pending_fault.producer_kind = ea_tag.producer_kind;
                    prov_pending_fault.ea_base_reg = ea_base_reg;
                    prov_pending_fault.ea_base_reg_val = ea_base_reg_val;
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
                if (!prov_pending_fault.detected) {
                    prov_pending_fault.detected = true;
                    prov_pending_fault.is_uaf = false;
                    prov_pending_fault.access_pc = pc;
                    prov_pending_fault.access_addr = addr;
                    prov_pending_fault.access_width = size;
                    prov_pending_fault.object_id = obj->object_id;
                    prov_pending_fault.generation = obj->generation;
                    prov_pending_fault.object_base = obj->base;
                    prov_pending_fault.requested_size = obj->requested_size;
                    prov_pending_fault.tracked_offset = offset;
                    prov_pending_fault.producer_pc = ea_tag.producer_pc;
                    prov_pending_fault.producer_kind = ea_tag.producer_kind;
                    prov_pending_fault.ea_base_reg = ea_base_reg;
                    prov_pending_fault.ea_base_reg_val = ea_base_reg_val;
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
             * extends past its end. */
            target_ulong region_end = mr->base + mr->size;
            /* Overflow-safe: if mr->base + mr->size wraps, the region is
             * invalid; treat as OK. */
            if (region_end >= mr->base) {
                /* Check addr + size > region_end overflow-safe:
                 * size > region_end - addr (when addr <= region_end). */
                if (addr <= region_end && addr + size > region_end &&
                    addr + size >= addr) {
                    /* Record non-fatal finding. */
                    if (!prov_pending_fault.detected) {
                        prov_pending_fault.detected = true;
                        prov_pending_fault.is_uaf = false;
                        prov_pending_fault.access_pc = pc;
                        prov_pending_fault.access_addr = addr;
                        prov_pending_fault.access_width = size;
                        prov_pending_fault.object_id = 0;
                        prov_pending_fault.generation = 0;
                        prov_pending_fault.object_base = mr->base;
                        prov_pending_fault.requested_size = mr->size;
                        prov_pending_fault.tracked_offset = (int64_t)(addr - mr->base);
                        prov_pending_fault.producer_pc = 0;
                        prov_pending_fault.producer_kind = PROV_PRODUCER_NONE;
                        prov_pending_fault.ea_base_reg = ea_base_reg;
                        prov_pending_fault.ea_base_reg_val = ea_base_reg_val;
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
    return &prov_pending_fault;
}

void provenance_clear_pending_fault(void) {
    memset(&prov_pending_fault, 0, sizeof(prov_pending_fault));
}

/* ---- Deferred crash finalization ---- */

bool provenance_finalize_fault(CPUArchState *env) {
    (void)env;
    return prov_pending_fault.detected;
}

const char *provenance_fault_reason(void) {
    if (!prov_pending_fault.detected) return NULL;
    return prov_pending_fault.is_uaf
        ? "memcheck: heap-use-after-free (provenance)"
        : "memcheck: heap-buffer-overflow (provenance)";
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
                         target_ulong dst_val) {
    provenance_propagate_mov(env, dst_idx, src_idx, 0, src_val, dst_val);
}

void helper_prov_lea_imm(CPUArchState *env, uint32_t dst_idx,
                         uint32_t base_idx, target_ulong disp,
                         target_ulong dst_val, target_ulong base_val) {
    provenance_lea_imm(env, dst_idx, base_idx, (int64_t)(int32_t)disp, 0,
                       dst_val, base_val);
}

void helper_prov_addsub_imm(CPUArchState *env, uint32_t reg_idx,
                            target_ulong delta, target_ulong pre_val,
                            target_ulong post_val) {
    provenance_addsub_imm(env, reg_idx, (int64_t)(int64_t)delta, 0,
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

void helper_prov_on_load(CPUArchState *env, uint32_t dst_idx,
                         target_ulong addr, target_ulong size) {
    if (size == sizeof(target_ulong)) {
        PtrTag mem_tag = provenance_mem_load_tag(addr);
        if (mem_tag.valid) {
            target_ulong actual_val = 0;
            void *h = g2h(addr);
            memcpy(&actual_val, h, sizeof(target_ulong));
            if (mem_tag.concrete_value == actual_val) {
                mem_tag.producer_pc = 0;
                mem_tag.producer_kind = PROV_PRODUCER_LOAD;
                provenance_set_reg_tag(env, dst_idx, mem_tag);
                return;
            }
        }
    }
    provenance_invalidate_reg(env, dst_idx, 0);
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

void helper_prov_check_access(CPUArchState *env, target_ulong addr,
                              target_ulong size, target_ulong pc,
                              uint32_t base_reg, uint32_t index_reg) {
    if (!binradar_memcheck_enabled) return;
    if (symbolic_start_code > 0 &&
        (pc < symbolic_start_code || pc >= symbolic_end_code)) {
        return;
    }
    PtrTag ea_tag = {0};
    target_ulong base_val = 0;
    if (base_reg != (uint32_t)-1 && base_reg < CPU_NB_REGS) {
        ea_tag = provenance_get_reg_tag(env, base_reg);
        base_val = env->regs[base_reg];
        if (ea_tag.valid) {
            /* EA = base + disp: fold the displacement into the tracked
             * offset (checked against overflow).  concrete_value stays
             * base_val so the value-consistency check passes. */
            int64_t disp = (int64_t)(addr - base_val);
            int64_t new_offset = ea_tag.concrete_offset + disp;
            if ((disp > 0 && new_offset < ea_tag.concrete_offset) ||
                (disp < 0 && new_offset > ea_tag.concrete_offset)) {
                ea_tag.valid = false;  /* overflow → UNKNOWN fallback */
            } else {
                ea_tag.concrete_offset = new_offset;
            }
        }
    }
    if (index_reg != (uint32_t)-1 && index_reg < CPU_NB_REGS) {
        PtrTag idx_tag = provenance_get_reg_tag(env, index_reg);
        if (idx_tag.valid) {
            if (ea_tag.valid) {
                /* Both base and index carry provenance (e.g. array indexing
                 * with a derived pointer): no sound way to fold a scaled
                 * index into one offset → UNKNOWN fallback. */
                ea_tag.valid = false;
            } else {
                target_ulong index_val = env->regs[index_reg];
                int64_t disp = (int64_t)(addr - index_val);
                int64_t new_offset = idx_tag.concrete_offset + disp;
                if ((disp > 0 && new_offset < idx_tag.concrete_offset) ||
                    (disp < 0 && new_offset > idx_tag.concrete_offset)) {
                    ea_tag.valid = false;
                } else {
                    ea_tag = idx_tag;
                    ea_tag.concrete_offset = new_offset;
                    base_val = index_val;
                }
            }
        }
    }
    provenance_check_access(env, addr, size, pc, ea_tag, base_reg, base_val);
}