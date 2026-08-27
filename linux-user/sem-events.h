#ifndef BINRADAR_SEM_EVENTS_H
#define BINRADAR_SEM_EVENTS_H

/*
 * Shared semantic-event layer (Stage 2.2).
 *
 * One neutral semantic-event API for the translator and non-translator
 * producers.  Provenance and OSPREY are separate consumers: neither
 * calls the other.  Every helper fan-out is defined here; the parallel
 * gen_prov_* / gen_osprey_* coverage switches in target/i386/translate.c
 * are replaced by single gen_sem_* dispatch points.
 *
 * Operation classes (SemOpClass): non-translator overwrite producers
 * label their events.  The helper manifest below records the neutral TCG
 * surface; unit tests require the classified and emittable sets to match.
 * UNKNOWN-class runtime events are fail-closed: conservative invalidation,
 * never a recorded OSPREY fact.  The producer matrix and structure-aware
 * source inventory cover direct, atomic, helper-backed, function-pointer,
 * helper-body, and explicitly unsupported dynamic producer families.  The
 * source gate is paired with runtime family validation and deterministic
 * control-region/cardinality checks; it is not a theorem about arbitrary
 * compiler-generated control flow.  Multipart events are buffered until their
 * final post-success constituent.
 */

#include "qemu/osdep.h"
#include "qemu.h"

/* ------------------------------------------------------------------ */
/* Operation-class manifest                                           */
/* ------------------------------------------------------------------ */

typedef enum SemOpClass {
    SEM_OP_INTEGER = 0,      /* integer ALU/mov/string/stack ops */
    SEM_OP_SIMD,             /* SSE/MMX/AVX stores */
    SEM_OP_X87_HELPER,       /* x87/FPU helper writes */
    SEM_OP_ATOMIC_RMW,       /* LOCKed RMW / atomic ops */
    SEM_OP_PAIRED,           /* multi-part stores (cmpxchg8b/16b, fsave) */
    SEM_OP_LIBC_MODEL,       /* libc-model memory writes (symbolic.c) */
    SEM_OP_SYSCALL,          /* syscall output buffers */
    SEM_OP_MAPPING,          /* brk/mmap/mremap/munmap */
    SEM_OP_SIGNAL,           /* signal frame/context writes */
    SEM_OP_SNAPSHOT,         /* snapshot mutation writes */
    SEM_OP_MPX,              /* MPX bound-table stores */
    SEM_OP_UNKNOWN,          /* fail-closed fallback (invalid) */
    SEM_OP_CLASS_COUNT
} SemOpClass;

typedef struct SemHelperClass {
    const char *helper_name; /* DEF_HELPER name (without "gen_helper_") */
    SemOpClass op_class;
} SemHelperClass;

typedef enum SemIntervalPolicy {
    SEM_INTERVAL_EXACT_WIDTH,
    SEM_INTERVAL_PAIRED,
    SEM_INTERVAL_RAW,
    SEM_INTERVAL_MULTIPART,
    SEM_INTERVAL_SPARSE,
    SEM_INTERVAL_DYNAMIC,
    SEM_INTERVAL_UNSUPPORTED,
} SemIntervalPolicy;

/* Stable IDs for the rows in sem_producer_table.  A translator/helper event
 * carries one ID in addition to its class and interval policy, so runtime
 * validation selects one manifest family instead of accepting a class-wide
 * width union.  The C unit test checks that table order and IDs stay aligned.
 */
typedef enum SemProducerId {
    SEM_PRODUCER_INTEGER_MODRM,
    SEM_PRODUCER_INTEGER_MOFFS,
    SEM_PRODUCER_INTEGER_STRING,
    SEM_PRODUCER_INTEGER_INS_OUTS,
    SEM_PRODUCER_INTEGER_STACK,
    SEM_PRODUCER_INTEGER_ENTER,
    SEM_PRODUCER_INTEGER_DESCRIPTOR,
    SEM_PRODUCER_ATOMIC_LOCK_RMW,
    SEM_PRODUCER_ATOMIC_XCHG,
    SEM_PRODUCER_PAIRED_CMPXCHG8B,
    SEM_PRODUCER_PAIRED_CMPXCHG16B,
    SEM_PRODUCER_SIMD_SCALAR,
    SEM_PRODUCER_SIMD_VECTOR,
    SEM_PRODUCER_SIMD_SPECIAL,
    SEM_PRODUCER_X87_SCALAR,
    SEM_PRODUCER_X87_RAW,
    SEM_PRODUCER_X87_ENVIRONMENT,
    SEM_PRODUCER_X87_SAVED_STATE,
    SEM_PRODUCER_X87_LEGACY_WIDTH_X86_64,
    SEM_PRODUCER_BOUND_LEGACY_X86_64,
    SEM_PRODUCER_MPX_BNDMOV,
    SEM_PRODUCER_MPX_BNDX_HELPER,
    SEM_PRODUCER_XSAVE_FXSAVE,
    SEM_PRODUCER_XSAVE_XSAVE,
    SEM_PRODUCER_MODEL_OUTPUT,
    SEM_PRODUCER_SYSCALL_OUTPUT,
    SEM_PRODUCER_MAPPING_OUTPUT,
    SEM_PRODUCER_SIGNAL_FRAME,
    SEM_PRODUCER_SNAPSHOT_WRITE,
    SEM_PRODUCER_SIMD_MASKMOV,
    SEM_PRODUCER_CONTROL_FAR,
    SEM_PRODUCER_CONTROL_IRET,
    SEM_PRODUCER_CONTROL_SEG_LOAD,
    SEM_PRODUCER_CONTROL_LLDT,
    SEM_PRODUCER_CONTROL_LTR,
    SEM_PRODUCER_CONTROL_SEG_QUERY,
    SEM_PRODUCER_CONTROL_IO_BITMAP,
    SEM_PRODUCER_CONTROL_SEG_HELPER,
    SEM_PRODUCER_BOUND_LEGACY,
    SEM_PRODUCER_COUNT,
    SEM_PRODUCER_INVALID = 0xff,
} SemProducerId;

/* The TCG helper ABI has six arguments.  Pack the producer's interval policy
 * and manifest-family ID into the unused high flags bits so runtime dispatch
 * validates the exact class/policy/width row that the source inventory checks.
 */
#define SEM_MEM_F_STORE           (1u << 0) /* store direction */
#define SEM_MEM_F_PROVENANCE_CHECK (1u << 1) /* run provenance EA check */
#define SEM_MEM_F_OSPREY_SKIP_F01 (1u << 2) /* provenance-only follow-up */
#define SEM_MEM_F_NO_EA           (1u << 3) /* plain F01; no EA decomposition */
#define SEM_MEM_POLICY_SHIFT 8
#define SEM_MEM_POLICY_MASK  (0x7u << SEM_MEM_POLICY_SHIFT)
#define SEM_MEM_PRODUCER_SHIFT 11
#define SEM_MEM_PRODUCER_MASK  (0x3fu << SEM_MEM_PRODUCER_SHIFT)
#define SEM_MEM_FLAGS_WITH_POLICY(_flags, _policy, _producer) \
    ((_flags) | ((uint32_t)(_policy) << SEM_MEM_POLICY_SHIFT) | \
     ((uint32_t)(_producer) << SEM_MEM_PRODUCER_SHIFT))

typedef struct SemProducerSpec {
    const char *producer;
    SemOpClass op_class;
    SemIntervalPolicy interval_policy;
    const uint32_t *interval_widths;
    uint32_t interval_width_count;
    bool supported;
    /* Comma-separated source ownership tokens.  Supported tokens carry
     * @SEM_INTERVAL_* so the source inventory binds each row to its event
     * policy; dynamic rows carry explicit file/API tokens. */
    const char *coverage;
} SemProducerSpec;

/* Class name + validity table (unit-testable manifest).  UNKNOWN is the
 * only invalid class: producers must never label events with it. */
extern const char *const sem_op_class_name[SEM_OP_CLASS_COUNT];
extern const bool sem_op_class_valid[SEM_OP_CLASS_COUNT];

/* Helper-name -> class coverage table: every sem_* TCG helper must be
 * registered here so new memory-writing helpers cannot silently bypass
 * the manifest.  Terminated by { NULL, 0 }. */
extern const SemHelperClass sem_helper_class_table[];

/* Declared Stage-2.2 producer-family matrix.  Fixed-width supported rows
 * carry every legal interval width; DYNAMIC rows deliberately have no fixed
 * list.  SPARSE and MULTIPART rows describe ordered interval policies rather
 * than inventing a contiguous extent.  Unsupported rows are explicit and
 * include a concrete coverage reason. */
extern const SemProducerSpec sem_producer_table[];

/* The exact set of helper names the translator is allowed to emit
 * (compile-checked by unit tests against translate.c usage). */
extern const char *const sem_emittable_helpers[];

/* True when any semantic-event consumer is active.  Stable after
 * startup; safe to gate TB translation on it. */
bool sem_events_active(void);

/* ------------------------------------------------------------------ */
/* C API: overwrite events (non-translator producers)                 */
/* ------------------------------------------------------------------ */

/* Route an accepted memory-overwrite interval through the shared
 * overwrite event BEFORE either consumer mutates its shadow.  The
 * class is validated against the manifest: an invalid class performs
 * conservative invalidation and never produces an OSPREY fact. */
void sem_mem_overwrite(target_ulong addr, target_ulong size,
                       SemOpClass cls);

/* The translator carries the operation class, interval policy, and manifest
 * family on every memory event.  The family is validated independently from
 * the class so overlapping producer rows cannot authorize one another. */
void sem_mem_access(CPUArchState *env, target_ulong addr,
                    target_ulong size, target_ulong pc, uint32_t flags,
                    SemOpClass cls, SemIntervalPolicy policy,
                    SemProducerId producer);

/* Helper-backed guest memory operation.  The helper calls this only after
 * its complete architectural interval succeeds. */
void sem_mem_helper_access(CPUArchState *env, target_ulong addr,
                           target_ulong size, target_ulong pc,
                           bool is_store, SemOpClass cls,
                           SemIntervalPolicy policy,
                           SemProducerId producer);

/* Publish one part of a helper-backed operation.  Parts are emitted only
 * after the helper's complete architectural operation succeeds.  A false
 * final_part preserves the instruction mode for the next ordered interval. */
void sem_mem_helper_access_part(CPUArchState *env, target_ulong addr,
                                target_ulong size, target_ulong pc,
                                bool is_store, SemOpClass cls,
                                SemIntervalPolicy policy,
                                SemProducerId producer, bool final_part);

/* MASKMOV writes only bytes whose mask MSB is set.  The helper publishes
 * one-byte intervals only after the complete helper succeeds; no partial
 * or contiguous full-width fact is invented for the sparse write. */
void sem_mem_maskmov(CPUArchState *env, target_ulong addr,
                     uint32_t selected_mask, uint32_t width,
                     target_ulong pc, SemOpClass cls,
                     SemIntervalPolicy policy, SemProducerId producer);

/* Register overwrite (snapshot reg mutation).  Same fail-closed rule. */
void sem_reg_overwrite(CPUArchState *env, int reg_idx, SemOpClass cls);

/* Full-register context replacement (signal delivery): kills every
 * register origin/tag and any in-flight EA metadata in both consumers. */
void sem_context_replace(CPUArchState *env);

/* Mark a successfully decoded but intentionally unsupported guest-memory
 * producer.  The active OSPREY sample is rejected; provenance remains
 * independent and continues its own conservative invalidation. */
void sem_mark_unsupported_execution(void);

/* Modeled-call boundary: invalidate the ABI caller-saved registers in
 * each active consumer before installing any explicit return origin. */
void sem_clobber_caller_saved(CPUArchState *env);

/* ------------------------------------------------------------------ */
/* TCG helper bodies are declared in target/i386/helper.h via DEF_HELPER
 * (translate.c sees them through exec/helper-proto.h).  sem-events.c
 * declares them manually to satisfy -Werror=missing-prototypes. */
/* ------------------------------------------------------------------ */

#endif /* BINRADAR_SEM_EVENTS_H */
