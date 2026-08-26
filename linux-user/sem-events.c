/*
 * Shared semantic-event layer (Stage 2.2).  See sem-events.h.
 *
 * Dispatch rules:
 *  - Every helper_* fan-out gates each consumer on its own active flag
 *    (binradar_memcheck_enabled for provenance, osprey_collect_enabled
 *    for OSPREY).  The translator-side gen_sem_* wrappers additionally
 *    gate on sem_events_active() so nothing is emitted when both
 *    consumers are off.
 *  - F01 policy (aflag == MO_64 && override < 0, main-image insn PC) is
 *    OSPREY consumer policy: helper_sem_set_ea records the mode, and
 *    helper_sem_mem_access's OSPREY branch applies the gate.  Provenance
 *    applies its own aflags/override rule inside helper_sem_check_access
 *    semantics (helper_prov_set_ea/check_access moved here verbatim).
 *  - Overwrite events (sem_mem_overwrite / sem_reg_overwrite /
 *    sem_context_replace) are fail-closed: UNKNOWN-class input performs
 *    conservative invalidation and never records an OSPREY fact.
 */

#include "qemu/osdep.h"

#include "sem-events.h"
#include "provenance.h"
#include "osprey.h"
#include "osprey-internal.h"
#include "snapshot.h"
#include "tcg/symbolic/symbolic-instrumentation.h"

/* Helper entry points (DEF_HELPER in target/i386/helper.h).  This TU
 * cannot include exec/helper-proto.h (target-specific); declare the
 * prototypes manually to satisfy -Werror=missing-prototypes. */
void helper_sem_reg_invalidate(CPUArchState *env, uint32_t reg_idx,
                               target_ulong pc);
void helper_sem_reg_copy(CPUArchState *env, uint32_t dst_idx,
                         uint32_t src_idx, target_ulong src_val,
                         target_ulong dst_val, target_ulong pc);
void helper_sem_reg_lea(CPUArchState *env, uint32_t dst_idx,
                        uint32_t base_idx, target_ulong disp,
                        target_ulong dst_val, target_ulong base_val);
void helper_sem_reg_lea_dyn(CPUArchState *env, uint32_t dst_idx,
                            uint32_t base_idx, target_ulong delta,
                            target_ulong dst_val, target_ulong base_val);
void helper_sem_reg_addsub_imm(CPUArchState *env, uint32_t reg_idx,
                               target_ulong delta, target_ulong pre_val,
                               target_ulong post_val, target_ulong pc);
void helper_sem_reg_addsub_reg(CPUArchState *env, uint32_t dst_idx,
                               uint32_t src_idx, target_ulong pc,
                               target_ulong dst_val, target_ulong src_val);
void helper_sem_reg_xchg(CPUArchState *env, uint32_t dst_idx,
                         uint32_t src_idx);
void helper_sem_clobber_caller_saved(CPUArchState *env);
void helper_sem_set_pc(CPUArchState *env, target_ulong pc);
void helper_sem_set_ea(CPUArchState *env, uint32_t base_reg,
                       uint32_t index_reg, uint32_t scale,
                       target_ulong disp, uint32_t mode);
void helper_sem_set_ea_vals(CPUArchState *env, target_ulong base_val,
                            target_ulong index_val);
void helper_sem_set_ea_mode(CPUArchState *env, uint32_t mode);
void helper_sem_mem_access(CPUArchState *env, target_ulong addr,
                           target_ulong size, target_ulong pc,
                           uint32_t flags, uint32_t cls);
void helper_sem_mem_overwrite(CPUArchState *env, target_ulong addr,
                              target_ulong size, uint32_t cls);
void helper_sem_on_load(CPUArchState *env, uint32_t dst_idx,
                        target_ulong addr, target_ulong size,
                        target_ulong pc, uint32_t cls);
void helper_sem_on_store(CPUArchState *env, uint32_t src_idx,
                         target_ulong addr, target_ulong size,
                         target_ulong src_val, uint32_t cls);
void helper_sem_call(CPUArchState *env, target_ulong callee_pc,
                     target_ulong entry_sp);
void helper_sem_ret(CPUArchState *env, target_ulong pc, target_ulong sp);
void helper_sem_rsp_update(CPUArchState *env, target_ulong new_sp,
                           target_ulong pc);

/* ------------------------------------------------------------------ */
/* Manifest                                                            */
/* ------------------------------------------------------------------ */

const char *const sem_op_class_name[SEM_OP_CLASS_COUNT] = {
    [SEM_OP_INTEGER]      = "SEM_OP_INTEGER",
    [SEM_OP_SIMD]         = "SEM_OP_SIMD",
    [SEM_OP_X87_HELPER]   = "SEM_OP_X87_HELPER",
    [SEM_OP_ATOMIC_RMW]   = "SEM_OP_ATOMIC_RMW",
    [SEM_OP_PAIRED]       = "SEM_OP_PAIRED",
    [SEM_OP_LIBC_MODEL]   = "SEM_OP_LIBC_MODEL",
    [SEM_OP_SYSCALL]      = "SEM_OP_SYSCALL",
    [SEM_OP_MAPPING]      = "SEM_OP_MAPPING",
    [SEM_OP_SIGNAL]       = "SEM_OP_SIGNAL",
    [SEM_OP_SNAPSHOT]     = "SEM_OP_SNAPSHOT",
    [SEM_OP_MPX]          = "SEM_OP_MPX",
    [SEM_OP_UNKNOWN]      = "SEM_OP_UNKNOWN",
};

const bool sem_op_class_valid[SEM_OP_CLASS_COUNT] = {
    [SEM_OP_INTEGER]    = true,
    [SEM_OP_SIMD]       = true,
    [SEM_OP_X87_HELPER] = true,
    [SEM_OP_ATOMIC_RMW] = true,
    [SEM_OP_PAIRED]     = true,
    [SEM_OP_LIBC_MODEL] = true,
    [SEM_OP_SYSCALL]    = true,
    [SEM_OP_MAPPING]    = true,
    [SEM_OP_SIGNAL]     = true,
    [SEM_OP_SNAPSHOT]   = true,
    [SEM_OP_MPX]        = true,
    [SEM_OP_UNKNOWN]    = false, /* fail-closed: never producer-labeled */
};

const SemProducerSpec sem_producer_table[] = {
    { "integer.modrm",       SEM_OP_INTEGER,    SEM_INTERVAL_EXACT_WIDTH, 8 },
    { "integer.moffs",       SEM_OP_INTEGER,    SEM_INTERVAL_EXACT_WIDTH, 8 },
    { "integer.string",      SEM_OP_INTEGER,    SEM_INTERVAL_EXACT_WIDTH, 8 },
    { "integer.ins-outs",    SEM_OP_INTEGER,    SEM_INTERVAL_EXACT_WIDTH, 8 },
    { "integer.stack-control", SEM_OP_INTEGER,  SEM_INTERVAL_EXACT_WIDTH, 8 },
    { "integer.descriptor",  SEM_OP_INTEGER,    SEM_INTERVAL_MULTIPART,  8 },
    { "atomic.lock-rmw",     SEM_OP_ATOMIC_RMW, SEM_INTERVAL_EXACT_WIDTH, 8 },
    { "atomic.xchg",         SEM_OP_ATOMIC_RMW, SEM_INTERVAL_EXACT_WIDTH, 8 },
    { "paired.cmpxchg8b",    SEM_OP_PAIRED,     SEM_INTERVAL_PAIRED,      8 },
    { "paired.cmpxchg16b",   SEM_OP_PAIRED,     SEM_INTERVAL_PAIRED,     16 },
    { "simd.scalar",         SEM_OP_SIMD,       SEM_INTERVAL_EXACT_WIDTH, 8 },
    { "simd.vector",         SEM_OP_SIMD,       SEM_INTERVAL_PAIRED,     16 },
    { "simd.special",        SEM_OP_SIMD,       SEM_INTERVAL_EXACT_WIDTH, 8 },
    { "x87.scalar",          SEM_OP_X87_HELPER, SEM_INTERVAL_EXACT_WIDTH, 8 },
    { "x87.raw",             SEM_OP_X87_HELPER, SEM_INTERVAL_RAW,         10 },
    { "x87.environment",     SEM_OP_X87_HELPER, SEM_INTERVAL_RAW,         14 },
    { "x87.saved-state",     SEM_OP_X87_HELPER, SEM_INTERVAL_RAW,         94 },
    { "mpx.bndmov",          SEM_OP_MPX,        SEM_INTERVAL_PAIRED,     16 },
    { "mpx.bndx-helper",     SEM_OP_MPX,        SEM_INTERVAL_MULTIPART,  12 },
    { "xsave.fxsave",        SEM_OP_PAIRED,     SEM_INTERVAL_RAW,        512 },
    { "xsave.xsave",         SEM_OP_PAIRED,     SEM_INTERVAL_RAW,          0 },
    { "model.output",        SEM_OP_LIBC_MODEL, SEM_INTERVAL_RAW,          1 },
    { "syscall.output",      SEM_OP_SYSCALL,    SEM_INTERVAL_RAW,          1 },
    { "mapping.output",      SEM_OP_MAPPING,    SEM_INTERVAL_RAW,          1 },
    { "signal.frame",        SEM_OP_SIGNAL,     SEM_INTERVAL_RAW,          1 },
    { "snapshot.write",      SEM_OP_SNAPSHOT,   SEM_INTERVAL_RAW,          1 },
    { NULL, 0, 0, 0 },
};

const SemHelperClass sem_helper_class_table[] = {
    { "sem_reg_invalidate",  SEM_OP_INTEGER },
    { "sem_reg_copy",        SEM_OP_INTEGER },
    { "sem_reg_lea",         SEM_OP_INTEGER },
    { "sem_reg_lea_dyn",     SEM_OP_INTEGER },
    { "sem_reg_addsub_imm",  SEM_OP_INTEGER },
    { "sem_reg_addsub_reg",  SEM_OP_INTEGER },
    { "sem_reg_xchg",        SEM_OP_INTEGER },
    { "sem_clobber_caller_saved", SEM_OP_INTEGER },
    { "sem_set_pc",          SEM_OP_INTEGER },
    { "sem_set_ea",          SEM_OP_INTEGER },
    { "sem_set_ea_vals",     SEM_OP_INTEGER },
    { "sem_set_ea_mode",     SEM_OP_INTEGER },
    { "sem_mem_access",      SEM_OP_INTEGER },
    { "sem_mem_overwrite",   SEM_OP_INTEGER },
    { "sem_on_load",         SEM_OP_INTEGER },
    { "sem_on_store",        SEM_OP_INTEGER },
    { "sem_call",            SEM_OP_INTEGER },
    { "sem_ret",             SEM_OP_INTEGER },
    { "sem_rsp_update",      SEM_OP_INTEGER },
    { NULL, 0 },
};

const char *const sem_emittable_helpers[] = {
    "sem_reg_invalidate",
    "sem_reg_copy",
    "sem_reg_lea",
    "sem_reg_lea_dyn",
    "sem_reg_addsub_imm",
    "sem_reg_addsub_reg",
    "sem_reg_xchg",
    "sem_clobber_caller_saved",
    "sem_set_pc",
    "sem_set_ea",
    "sem_set_ea_vals",
    "sem_set_ea_mode",
    "sem_mem_access",
    "sem_mem_overwrite",
    "sem_on_load",
    "sem_on_store",
    "sem_call",
    "sem_ret",
    "sem_rsp_update",
    NULL,
};

bool sem_events_active(void) {
    return binradar_memcheck_enabled != 0 || osprey_collect_enabled != 0;
}

static bool sem_op_class_is_valid(SemOpClass cls) {
    return (unsigned int)cls < SEM_OP_CLASS_COUNT &&
           sem_op_class_valid[(unsigned int)cls];
}

static void osprey_clear_ea(OspreyCpuOriginState *st, bool clear_mode);

/* ------------------------------------------------------------------ */
/* Overwrite events (C API)                                           */
/* ------------------------------------------------------------------ */

void sem_mem_overwrite(target_ulong addr, target_ulong size,
                       SemOpClass cls) {
    bool valid_class = sem_op_class_is_valid(cls);
    /* Invalid classes still invalidate active consumer state, but can
     * never authorize an OSPREY fact or a more precise transfer. */
    if (binradar_memcheck_enabled) {
        provenance_on_modify_mem(addr, size);
    }
    /* OSPREY consumer (Stage 2.2): documented no-op — no mem-slot
     * invalidation exists; shadow invalidation is Stage 2.4. */
    (void)valid_class;
}

void sem_reg_overwrite(CPUArchState *env, int reg_idx, SemOpClass cls) {
    bool valid_class = sem_op_class_is_valid(cls);
    if (env == NULL || reg_idx < 0 || reg_idx >= CPU_NB_REGS) {
        return;
    }
    if (binradar_memcheck_enabled) {
        provenance_on_modify_reg(env, reg_idx);
    }
    if (osprey_collect_enabled) {
        osprey_on_reg_invalidate(env, (uint32_t)reg_idx);
    }
    (void)valid_class;
}

void sem_context_replace(CPUArchState *env) {
    if (env == NULL) {
        return;
    }
    if (binradar_memcheck_enabled) {
        provenance_invalidate_all_regs(env);
    }
    if (osprey_collect_enabled) {
        OspreyCpuOriginState *st = osprey_cpu_origin(env);
        /* A fault can leave pre-access EA metadata unconsumed.  A signal
         * or restored context is a hard boundary; no later access may
         * reuse that record. */
        osprey_clear_ea(st, true);
        for (int i = 0; i < CPU_NB_REGS; i++) {
            osprey_on_reg_invalidate(env, (uint32_t)i);
        }
    }
}

void sem_clobber_caller_saved(CPUArchState *env) {
    static const int caller_saved[] = {
        R_EAX, R_ECX, R_EDX, R_ESI, R_EDI,
#ifdef TARGET_X86_64
        R_R8, R_R9, R_R10, R_R11,
#endif
    };
    if (env == NULL) {
        return;
    }
    if (binradar_memcheck_enabled) {
        provenance_clobber_caller_saved(env);
    }
    if (osprey_collect_enabled) {
        for (size_t i = 0; i < G_N_ELEMENTS(caller_saved); i++) {
            osprey_on_reg_invalidate(env, (uint32_t)caller_saved[i]);
        }
    }
}

/* ------------------------------------------------------------------ */
/* TCG helpers — provenance consumer                                  */
/* ------------------------------------------------------------------ */

static void sem_prov_invalidate_reg(CPUArchState *env, uint32_t reg_idx,
                                    target_ulong pc) {
    provenance_invalidate_reg(env, reg_idx, pc);
}

static void sem_prov_reg_copy(CPUArchState *env, uint32_t dst_idx,
                              uint32_t src_idx, target_ulong src_val,
                              target_ulong dst_val, target_ulong pc) {
    provenance_propagate_mov(env, dst_idx, src_idx, pc, src_val, dst_val);
}

static void sem_prov_reg_lea(CPUArchState *env, uint32_t dst_idx,
                             uint32_t base_idx, int64_t disp,
                             target_ulong dst_val, target_ulong base_val) {
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    target_ulong pc = shadow->cur_pc;
    provenance_lea_imm(env, dst_idx, base_idx, disp, pc, dst_val, base_val);
}

static void sem_prov_reg_addsub_imm(CPUArchState *env, uint32_t reg_idx,
                                    int64_t delta, target_ulong pre_val,
                                    target_ulong post_val,
                                    target_ulong pc) {
    provenance_addsub_imm(env, reg_idx, delta, pc, pre_val, post_val);
}

static void sem_prov_reg_addsub_reg(CPUArchState *env, uint32_t dst_idx,
                                    uint32_t src_idx, target_ulong pc,
                                    target_ulong dst_val,
                                    target_ulong src_val) {
    int is_sub = (dst_idx >> 16) & 1;
    provenance_addsub_reg(env, dst_idx & 0xffff, src_idx, is_sub, pc,
                          dst_val, src_val);
}

static void sem_prov_reg_xchg(CPUArchState *env, uint32_t dst_idx,
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

static void sem_prov_on_load(CPUArchState *env, uint32_t dst_idx,
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
            if (provenance_debug) {
                log_msg("[prov] [consistency] mem value mismatch [tag %lx] [mem %lx] [addr %lx] [pc %lx]\n",
                        mem_tag.concrete_value, actual_val, addr, pc);
            }
            provenance_mem_invalidate(addr, sizeof(target_ulong));
        }
    }
    provenance_invalidate_reg(env, dst_idx, pc);
}

static void sem_prov_on_store(CPUArchState *env, uint32_t src_idx,
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

/* EA metadata + access check (moved verbatim from helper_prov_set_ea /
 * helper_prov_check_access). */
static void sem_prov_set_ea(CPUArchState *env, uint32_t base_reg,
                            uint32_t index_reg, uint32_t scale,
                            target_ulong disp, uint32_t mode) {
    PtrRegShadow *shadow = provenance_get_reg_shadow(env);
    shadow->ea_meta.base_reg = (int32_t)base_reg;
    shadow->ea_meta.index_reg = (int32_t)index_reg;
    shadow->ea_meta.scale = (int32_t)scale;
    shadow->ea_meta.disp = (target_long)disp;
    shadow->ea_meta.aflags = mode & 0xff;
    shadow->ea_meta.override = (int32_t)((mode >> 8) & 0x7fffffff) - 1;
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

static void sem_prov_check_access(CPUArchState *env, target_ulong addr,
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
    uint32_t aflags = shadow->ea_meta.aflags;
    int override = shadow->ea_meta.override;
    /* Pre-access snapshots taken by sem_set_ea (before the guest
     * load/store), so a self-overwriting load cannot corrupt them. */
    PtrTag base_tag = shadow->ea_meta.base_tag;
    PtrTag index_tag = shadow->ea_meta.index_tag;
    target_ulong base_val = shadow->ea_meta.base_val;
    target_ulong index_val = shadow->ea_meta.index_val;
    shadow->ea_meta.valid = false;
    if (have_ea) {
        /* Semantic EA propagation (§6).  Identity requires a 64-bit
         * address size with no segment override.  Constant displacement
         * forms propagate directly.  For benchmark compatibility, a
         * tagged base plus an untagged runtime index also propagates only
         * after exact target-width EA reconstruction succeeds; two tagged
         * inputs remain UNKNOWN.  Truncating address modes, unmodeled
         * segment bases, and a tagged scaled index remain UNKNOWN and use
         * exact-bounds fallback only. */
        if (aflags != MO_64 || override >= 0) {
            provenance_check_access(env, addr, size, pc, (PtrTag){0},
                                    -1, 0);
            return;
        }
        if (base_reg >= 0 && base_reg < CPU_NB_REGS) {
            if (index_reg < 0 && base_tag.valid) {
                /* [base + disp]: the access address must equal
                 * base_val + disp (semantic, translation-time disp).
                 * x86 address arithmetic wraps mod 2^64, so the
                 * expected address is computed with wrapping unsigned
                 * arithmetic (a negative displacement is a full-width
                 * sign-extended value, not an overflow); only the
                 * tracked-offset fold below uses checked overflow. */
                target_ulong expect = base_val + (target_ulong)disp;
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
            if (index_reg >= 0 && base_tag.valid) {
                /* base + index: two-register form.  If BOTH carry valid
                 * tags there is no sound merge rule — UNKNOWN.  If only
                 * the base is tagged, the index is a pure integer
                 * offset: the address must match the semantic
                 * decomposition exactly (scale is the SIB shift 0..3),
                 * and only then is the runtime delta addr - base_val
                 * folded into the tracked offset with checked
                 * arithmetic.  This is a verified arithmetic fold, not
                 * a numeric proximity guess (§6). */
                if (index_tag.valid) {
                    /* Two tagged inputs: no sound merge (§6). */
                    provenance_check_access(env, addr, size, pc,
                                            (PtrTag){0}, -1, 0);
                    return;
                }
                /* Untagged index: semantic exact-match, then fold the
                 * runtime delta into the tracked offset (checked).
                 * Expected-address arithmetic is wrapping (x86 mod
                 * 2^64); only the offset fold is overflow-checked. */
                target_ulong expect = base_val +
                    ((target_ulong)index_val << scale) +
                    (target_ulong)disp;
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
             * equal index_val + disp (wrapping arithmetic). */
            if (index_tag.valid && scale == 0) {
                target_ulong expect = index_val + (target_ulong)disp;
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

/* ------------------------------------------------------------------ */
/* TCG helpers — OSPREY consumer                                      */
/* ------------------------------------------------------------------ */

/* F01 gate: facts are recorded only for accesses whose instruction runs
 * in a 64-bit address mode without segment override.  The mode is part
 * of the EA event payload; when set_ea was not emitted (no EA
 * decomposition, e.g. push/pop), the access event still carries the
 * current instruction's mode so F01 recording can be gated. */
static inline bool osprey_mode_ok(uint32_t mode) {
    uint32_t aflags = mode & 0xff;
    int32_t override = (int32_t)((mode >> 8) & 0x7fffffff) - 1;
    return aflags == MO_64 && override < 0;
}

/* Drop every pending EA field without touching register or memory origins.
 * Keep the mode optionally: plain F01 events use it for their mode gate
 * while deliberately discarding any decomposed EA record. */
static void osprey_clear_ea(OspreyCpuOriginState *st, bool clear_mode) {
    st->ea_valid = false;
    st->ea_base_reg = 0;
    st->ea_index_reg = 0;
    st->ea_scale = 0;
    st->ea_disp = 0;
    st->ea_base_val = 0;
    st->ea_index_val = 0;
    if (clear_mode) {
        st->ea_mode = 0;
    }
    memset(&st->ea_base_origin, 0, sizeof(st->ea_base_origin));
    memset(&st->ea_index_origin, 0, sizeof(st->ea_index_origin));
}

void helper_sem_set_ea(CPUArchState *env, uint32_t base_reg,
                       uint32_t index_reg, uint32_t scale,
                       target_ulong disp, uint32_t mode) {
    if (binradar_memcheck_enabled) {
        /* Reads env->regs for the snapshots exactly like the old
         * helper_prov_set_ea (behavior preserved verbatim). */
        sem_prov_set_ea(env, base_reg, index_reg, scale, disp, mode);
    }
    if (osprey_collect_enabled) {
        OspreyCpuOriginState *st = osprey_cpu_origin(env);
        st->ea_mode = mode;
        if (!osprey_mode_ok(mode)) {
            /* Not an F01-eligible mode: record nothing (stale record
             * protection). */
            osprey_clear_ea(st, true);
            return;
        }
        uint32_t packed = 0x80000000u;
        packed |= (uint32_t)(base_reg + 1) << 16;
        packed |= (uint32_t)(index_reg + 1) << 8;
        packed |= (uint32_t)scale;
        st->ea_valid = (packed & 0x80000000u) != 0;
        st->ea_base_reg = (int32_t)((packed >> 16) & 0xff) - 1;
        st->ea_index_reg = (int32_t)((packed >> 8) & 0xff) - 1;
        st->ea_scale = (int32_t)(packed & 0xff);
        st->ea_disp = (int64_t)(int32_t)disp;
        st->ea_base_val = 0;
        st->ea_index_val = 0;
        /* Values + origin snapshots arrive in helper_sem_set_ea_vals
         * (emitted immediately after by the gen_sem_set_ea wrapper):
         * env->regs may be stale inside helpers, so the base/index
         * concrete values must ride as explicit TCG args. */
    }
}

void helper_sem_set_ea_mode(CPUArchState *env, uint32_t mode) {
    if (!osprey_collect_enabled) {
        return;
    }
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    st->ea_mode = mode;
    if (!osprey_mode_ok(mode)) {
        osprey_clear_ea(st, true);
    }
}

void helper_sem_set_ea_vals(CPUArchState *env, target_ulong base_val,
                            target_ulong index_val) {
    if (!osprey_collect_enabled) {
        return;
    }
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    if (!st->ea_valid) {
        return; /* mode-ineligible or no EA record: nothing to fill */
    }
    st->ea_base_val = base_val;
    st->ea_index_val = index_val;
    /* Snapshot the base/index origins NOW: the registers may be killed
     * by the access itself before the mem-access event consumes the EA
     * (e.g. mov (%rax),%rax). */
    memset(&st->ea_base_origin, 0, sizeof(st->ea_base_origin));
    memset(&st->ea_index_origin, 0, sizeof(st->ea_index_origin));
    if (st->ea_base_reg >= 0 && st->ea_base_reg < CPU_NB_REGS) {
        st->ea_base_origin = st->regs[st->ea_base_reg];
    }
    if (st->ea_index_reg >= 0 && st->ea_index_reg < CPU_NB_REGS) {
        st->ea_index_origin = st->regs[st->ea_index_reg];
    }
}

void sem_mem_access(CPUArchState *env, target_ulong addr,
                    target_ulong size, target_ulong pc, uint32_t flags,
                    SemOpClass cls) {
    bool valid_class = sem_op_class_is_valid(cls);
    uint32_t is_store = flags & 1;
    /* The provenance access check runs only at sites that emitted it
     * historically (check bit set): those are exactly the EA-decomposed
     * sites.  F01-only sites (SIMD/x87/atomic/paired) must not add new
     * provenance findings. */
    if ((flags & 2) && binradar_memcheck_enabled) {
        sem_prov_check_access(env, addr, size, pc);
    }
    if (!osprey_collect_enabled) {
        return;
    }
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    if (flags & 8) {
        /* Plain producer events have no EA decomposition.  Discard a
         * fault-left record before recording the successful interval. */
        osprey_clear_ea(st, false);
    }
    if (!valid_class || (flags & 4)) {
        osprey_clear_ea(st, true);
        return;
    }
    /* F01 gate: the current instruction must be mode-eligible.  The EA
     * record (if any) was stored by helper_sem_set_ea with its own mode;
     * when no set_ea ran (push/pop), ea_mode carries the instruction's
     * mode so F01 is still gated correctly.  The mode is consumed here:
     * a stale record can never gate a later instruction's access. */
    uint32_t mode = st->ea_mode;
    st->ea_mode = 0; /* consumed */
    if (!osprey_mode_ok(mode)) {
        osprey_clear_ea(st, true);
        return;
    }
    osprey_on_mem_access(env, addr, (uint64_t)size, (uint64_t)pc,
                         is_store);
}

void helper_sem_mem_access(CPUArchState *env, target_ulong addr,
                           target_ulong size, target_ulong pc,
                           uint32_t flags, uint32_t cls) {
    sem_mem_access(env, addr, size, pc, flags, (SemOpClass)cls);
}

void helper_sem_mem_overwrite(CPUArchState *env, target_ulong addr,
                              target_ulong size, uint32_t cls) {
    sem_mem_overwrite(addr, size, (SemOpClass)cls);
}

void sem_mem_helper_access(CPUArchState *env, target_ulong addr,
                           target_ulong size, target_ulong pc,
                           bool is_store, SemOpClass cls) {
    sem_mem_access(env, addr, size, pc, (is_store ? 1u : 0u) | 8u, cls);
}

void helper_sem_on_load(CPUArchState *env, uint32_t dst_idx,
                        target_ulong addr, target_ulong size,
                        target_ulong pc, uint32_t cls) {
    if (!sem_op_class_is_valid((SemOpClass)cls)) {
        if (binradar_memcheck_enabled) {
            sem_prov_on_load(env, dst_idx, addr, size, pc);
        }
        if (osprey_collect_enabled && dst_idx < CPU_NB_REGS) {
            osprey_on_reg_invalidate(env, dst_idx);
        }
        if (osprey_collect_enabled) {
            osprey_clear_ea(osprey_cpu_origin(env), true);
        }
        return;
    }
    if (binradar_memcheck_enabled) {
        sem_prov_on_load(env, dst_idx, addr, size, pc);
    }
    if (!osprey_collect_enabled) {
        return;
    }
    /* Aligned native-width reload: restore the origin into dst_reg. */
    if (size == OSPREY_SHADOW_ALIGN && (addr & (OSPREY_SHADOW_ALIGN - 1)) == 0) {
        target_ulong value = 0;
        if (is_valid_address(addr, false)) {
            memcpy(&value, g2h(addr), sizeof(value));
        }
        osprey_on_mem_load_origin(env, dst_idx, addr, value);
    }
}

void helper_sem_on_store(CPUArchState *env, uint32_t src_idx,
                         target_ulong addr, target_ulong size,
                         target_ulong src_val, uint32_t cls) {
    if (!sem_op_class_is_valid((SemOpClass)cls)) {
        if (binradar_memcheck_enabled) {
            provenance_mem_invalidate(addr, size);
        }
        if (osprey_collect_enabled) {
            /* Unknown stores cannot transfer an origin.  Route an
             * impossible source index through the normal store path so
             * the OSPREY memory shadow is overwritten with an invalid
             * origin instead of retaining stale metadata. */
            osprey_on_mem_store_origin(env, CPU_NB_REGS, addr, size,
                                       src_val);
            osprey_clear_ea(osprey_cpu_origin(env), true);
        }
        return;
    }
    if (binradar_memcheck_enabled) {
        sem_prov_on_store(env, src_idx, addr, size);
    }
    if (!osprey_collect_enabled) {
        return;
    }
    osprey_on_mem_store_origin(env, src_idx, addr, size, src_val);
}

void helper_sem_reg_invalidate(CPUArchState *env, uint32_t reg_idx,
                               target_ulong pc) {
    if (binradar_memcheck_enabled) {
        sem_prov_invalidate_reg(env, reg_idx, pc);
    }
    if (osprey_collect_enabled) {
        osprey_on_reg_invalidate(env, reg_idx);
    }
}

void helper_sem_reg_copy(CPUArchState *env, uint32_t dst_idx,
                         uint32_t src_idx, target_ulong src_val,
                         target_ulong dst_val, target_ulong pc) {
    if (binradar_memcheck_enabled) {
        sem_prov_reg_copy(env, dst_idx, src_idx, src_val, dst_val, pc);
    }
    if (osprey_collect_enabled) {
        osprey_on_reg_copy(env, dst_idx, src_idx, src_val, dst_val);
    }
}

void helper_sem_reg_lea(CPUArchState *env, uint32_t dst_idx,
                        uint32_t base_idx, target_ulong disp,
                        target_ulong dst_val, target_ulong base_val) {
    if (binradar_memcheck_enabled) {
        sem_prov_reg_lea(env, dst_idx, base_idx, (int64_t)disp,
                         dst_val, base_val);
    }
    if (osprey_collect_enabled) {
        osprey_on_reg_lea(env, dst_idx, base_idx, (int64_t)disp,
                          dst_val, base_val);
    }
}

void helper_sem_reg_lea_dyn(CPUArchState *env, uint32_t dst_idx,
                            uint32_t base_idx, target_ulong delta,
                            target_ulong dst_val, target_ulong base_val) {
    if (binradar_memcheck_enabled) {
        sem_prov_reg_lea(env, dst_idx, base_idx, (int64_t)delta,
                         dst_val, base_val);
    }
    /* Indexed-address policy belongs to Stage 2.3.  Until then the
     * destination must be killed, not left carrying a stale origin when
     * provenance requested write-back suppression. */
    if (osprey_collect_enabled) {
        osprey_on_reg_invalidate(env, dst_idx);
    }
}

void helper_sem_reg_addsub_imm(CPUArchState *env, uint32_t reg_idx,
                               target_ulong delta, target_ulong pre_val,
                               target_ulong post_val, target_ulong pc) {
    if (binradar_memcheck_enabled) {
        sem_prov_reg_addsub_imm(env, reg_idx, (int64_t)delta, pre_val,
                                post_val, pc);
    }
    /* Stage 2.3 will define accepted address folds.  Conservatively kill
     * the destination now so the shared suppression bit cannot preserve
     * a stale OSPREY origin. */
    if (osprey_collect_enabled) {
        osprey_on_reg_invalidate(env, reg_idx);
    }
}

void helper_sem_reg_addsub_reg(CPUArchState *env, uint32_t dst_idx,
                               uint32_t src_idx, target_ulong pc,
                               target_ulong dst_val, target_ulong src_val) {
    if (binradar_memcheck_enabled) {
        sem_prov_reg_addsub_reg(env, dst_idx, src_idx, pc, dst_val,
                                src_val);
    }
    if (osprey_collect_enabled) {
        osprey_on_reg_invalidate(env, dst_idx & 0xffffu);
    }
}

void helper_sem_reg_xchg(CPUArchState *env, uint32_t dst_idx,
                         uint32_t src_idx) {
    if (binradar_memcheck_enabled) {
        sem_prov_reg_xchg(env, dst_idx, src_idx);
    }
    /* The address-origin swap policy is Stage 2.3.  Killing both sides is
     * sound and avoids retaining pre-exchange identities. */
    if (osprey_collect_enabled) {
        osprey_on_reg_invalidate(env, dst_idx);
        osprey_on_reg_invalidate(env, src_idx);
    }
}

void helper_sem_set_pc(CPUArchState *env, target_ulong pc) {
    /* Provenance scratch PC for lea_imm (OSPREY has no equivalent). */
    if (binradar_memcheck_enabled) {
        PtrRegShadow *shadow = provenance_get_reg_shadow(env);
        shadow->cur_pc = pc;
    }
}

void helper_sem_call(CPUArchState *env, target_ulong callee_pc,
                     target_ulong entry_sp) {
    if (osprey_collect_enabled) {
        osprey_on_call(env, callee_pc, entry_sp);
    }
}

void helper_sem_ret(CPUArchState *env, target_ulong pc, target_ulong sp) {
    if (osprey_collect_enabled) {
        osprey_on_ret(env, pc, sp);
    }
}

void helper_sem_rsp_update(CPUArchState *env, target_ulong new_sp,
                           target_ulong pc) {
    if (osprey_collect_enabled) {
        osprey_on_rsp_update(env, new_sp, pc);
    }
}

void helper_sem_clobber_caller_saved(CPUArchState *env) {
    sem_clobber_caller_saved(env);
}
