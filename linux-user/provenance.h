/*
 * provenance.h — Runtime pointer-provenance shadow state for heap OOB/UAF.
 *
 * Key design: tags are keyed by guest architectural register number
 * (env->regs[i]) and by guest-memory address (for pointer spills),
 * NOT by TCG temporary index.  This makes tags survive TB boundaries
 * and avoids the stale-tag problem that broke the s_alloc_id approach.
 */
#ifndef PROVENANCE_H
#define PROVENANCE_H

#include "qemu/osdep.h"
#include "cpu.h"
#include "snapshot.h"

/* ---- Types ---- */

typedef enum {
    PROV_PRODUCER_NONE = 0,
    PROV_PRODUCER_MALLOC_RETURN,
    PROV_PRODUCER_CALLOC_RETURN,
    PROV_PRODUCER_REALLOC_RETURN,
    PROV_PRODUCER_MOV,
    PROV_PRODUCER_LEA,
    PROV_PRODUCER_ADD_IMM,
    PROV_PRODUCER_SUB_IMM,
    PROV_PRODUCER_LOAD,
    PROV_PRODUCER_STACK_RELOAD,
    PROV_PRODUCER_CALL_RETURN,
} PtrProducerKind;

typedef enum {
    PROV_OBJ_LIVE  = 0,
    PROV_OBJ_FREED = 1,
} ProvenanceObjState;

typedef enum {
    PROV_OP_NONE = 0,
    PROV_OP_MALLOC,
    PROV_OP_CALLOC,
    PROV_OP_REALLOC,
    PROV_OP_FREE,
} ProvenancePendingKind;

/* Runtime pointer tag attached to a guest GPR or a memory slot. */
typedef struct PtrTag {
    uint64_t        object_id;      /* logical allocation identity         */
    uint32_t        generation;     /* generation to detect reuse at same base */
    int64_t         concrete_offset;/* offset from object->base            */
    target_ulong    concrete_value; /* actual pointer value in the register*/
    target_ulong    producer_pc;    /* PC of the op that created this tag  */
    PtrProducerKind producer_kind;  /* how the tag was produced            */
    bool            valid;          /* false = UNKNOWN (no provenance)     */
} PtrTag;

/* Allocation object metadata.  Lives in a persistent table keyed by
 * {object_id, generation} and a separate live-by-base index. */
typedef struct ProvenanceObject {
    uint64_t              object_id;
    uint32_t              generation;
    target_ulong          base;
    target_ulong          requested_size;
    target_ulong          alloc_pc;
    ProvenanceObjState    state;
} ProvenanceObject;

/* Pending allocator operation (call entry, not yet returned). */
typedef struct {
    bool                   valid;
    bool                   overflowed;    /* calloc: n*size overflowed */
    ProvenancePendingKind  kind;
    target_ulong           call_pc;
    target_ulong           arg_size;       /* malloc/calloc total           */
    target_ulong           arg_ptr;        /* realloc/free old pointer      */
    uint64_t               old_object_id;  /* realloc: old object identity  */
    uint32_t               old_generation; /* realloc: old generation       */
} ProvenancePending;

/* Per-CPU register shadow.  Stored as a pointer inside CPUArchState
 * (allocated lazily) so it is automatically copy-on-write across fork. */
typedef struct PtrRegShadow {
    PtrTag       gpr[CPU_NB_REGS];
    target_ulong last_writer_pc[CPU_NB_REGS];
    /* Current instruction PC scratch: set by helper_prov_set_pc before
     * transfer helpers whose argument list is full (LEA), so producer
     * metadata carries the exact guest instruction PC, not a truncated
     * low-16-bits approximation. */
    target_ulong cur_pc;
    /* Pending allocator operation for this guest thread (per-CPU, so
     * multithreaded guests keep independent pending ops). */
    ProvenancePending pending;
    /* Effective-address metadata for the in-flight access check.  Set by
     * helper_prov_set_ea BEFORE the guest load/store (translation-time
     * metadata), consumed by helper_prov_check_access AFTER it, so a
     * faulting access never records a finding.
     *
     * The base/index concrete values and tags are SNAPSHOTTED at set_ea
     * time (before the memory op).  A load whose destination overwrites
     * its own EA base/index register (e.g. `mov (%rax), %rax`) must not
     * make the post-access check observe the loaded value/tag instead of
     * the address-producing state (§6). */
    struct ProvEAMeta {
        int32_t      base_reg;   /* -1 if no base register              */
        int32_t      index_reg;  /* -1 if no index register             */
        int32_t      scale;      /* SIB scale: 0=*1 1=*2 2=*4 3=*8      */
        target_long  disp;       /* constant displacement               */
        target_ulong base_val;   /* pre-access concrete base value      */
        target_ulong index_val;  /* pre-access concrete index value     */
        PtrTag       base_tag;   /* pre-access base register tag        */
        PtrTag       index_tag;  /* pre-access index register tag       */
        bool         valid;      /* set by prov_set_ea, consumed by check */
    } ea_meta;
} PtrRegShadow;

/* Memory shadow entry: maps an aligned 8-byte guest slot to a PtrTag. */
typedef struct PtrMemEntry {
    target_ulong  addr;       /* aligned 8-byte address */
    PtrTag        tag;
} PtrMemEntry;

/* Pending provenance fault (non-fatal, deferred crash). */
typedef struct {
    bool            detected;
    bool            reported;   /* structured finding line already emitted */
    target_ulong    access_pc;
    target_ulong    access_addr;
    uint32_t        access_width;
    uint64_t        object_id;
    uint32_t        generation;
    target_ulong    object_base;
    target_ulong    requested_size;
    int64_t         tracked_offset;
    target_ulong    producer_pc;
    PtrProducerKind producer_kind;
    target_ulong    last_writer_pc;   /* shadow last_writer_pc[ea_base_reg] */
    target_ulong    ea_base_reg_val;
    int             ea_base_reg;       /* -1 if unknown */
    bool            is_uaf;
    /* Final solver cursors at finding time (child side, valid in the
     * parent after fork because the pools are attached before fork at the
     * same addresses).  Published by the timeout path (§P1). */
    uintptr_t       next_query;
    uintptr_t       next_free_expr;
} PendingProvenanceFault;

/* ---- Initialization ---- */
void provenance_init(void);
PtrRegShadow *provenance_get_reg_shadow(CPUArchState *env);

/* ---- Allocation object management ---- */
/* Called on successful malloc/calloc return: create LIVE object, return tag. */
PtrTag provenance_create_object(target_ulong base, target_ulong size,
                                target_ulong pc, PtrProducerKind kind);
/* Called on free: mark object FREED.  Returns true if found. */
bool provenance_retire_object(target_ulong base);
/* Look up object by {object_id, generation}.  Returns NULL if absent. */
ProvenanceObject *provenance_lookup_object(uint64_t object_id,
                                           uint32_t generation);
/* Look up live object by base address (for exact-bounds fallback). */
ProvenanceObject *provenance_lookup_live_by_base(target_ulong base);

/* ---- Pending allocator operations ---- */
void provenance_set_pending(CPUArchState *env, ProvenancePendingKind kind,
                            target_ulong call_pc, target_ulong arg_size,
                            target_ulong arg_ptr);
ProvenancePending provenance_get_pending(CPUArchState *env,
                                         target_ulong call_pc);
void provenance_clear_pending(CPUArchState *env);

/* ---- Register tag operations ---- */
/* Invalidate a register's tag (set to UNKNOWN). */
void provenance_invalidate_reg(CPUArchState *env, int reg_idx, target_ulong pc);
/* Invalidate every GPR tag (signal delivery/return, context switches). */
void provenance_invalidate_all_regs(CPUArchState *env);
/* Set a register's tag from an explicit PtrTag. */
void provenance_set_reg_tag(CPUArchState *env, int reg_idx, PtrTag tag);
void provenance_addsub_reg(CPUArchState *env, int dst_idx, int src_idx,
                           int is_sub, target_ulong pc,
                           target_ulong dst_val, target_ulong src_val);
/* Get a register's tag (returns valid=false if UNKNOWN). */
PtrTag provenance_get_reg_tag(CPUArchState *env, int reg_idx);
/* Propagate tag from src to dst (full 64-bit mov). */
void provenance_propagate_mov(CPUArchState *env, int dst_idx, int src_idx,
                              target_ulong pc, target_ulong src_val,
                              target_ulong dst_val);
/* Apply lea dst, [base + disp]: tag(dst) = tag(base) with offset += disp. */
void provenance_lea_imm(CPUArchState *env, int dst_idx, int base_idx,
                        int64_t disp, target_ulong pc,
                        target_ulong dst_val, target_ulong base_val);
/* Apply add/sub dst, imm: if dst has valid tag, update offset. */
void provenance_addsub_imm(CPUArchState *env, int reg_idx, int64_t delta,
                           target_ulong pc, target_ulong pre_val,
                           target_ulong post_val);
/* Invalidate all caller-saved registers (ABI clobber at call return). */
void provenance_clobber_caller_saved(CPUArchState *env);

/* ---- Memory shadow operations ---- */
/* Store a pointer tag at an aligned address. */
void provenance_mem_store_tag(target_ulong addr, PtrTag tag);
/* Load a pointer tag from an aligned address.  Returns valid=false if none. */
PtrTag provenance_mem_load_tag(target_ulong addr);
/* Invalidate overlapping shadow entries (for non-pointer stores). */
void provenance_mem_invalidate(target_ulong addr, target_ulong size);

/* ---- Access checking ---- */
/* Check an access using provenance tag.  Returns MemcheckResult.
 * If tag is UNKNOWN, falls through to exact-bounds on live objects.
 * Records a non-fatal PendingProvenanceFault on OOB/UAF. */
MemcheckResult provenance_check_access(CPUArchState *env, target_ulong addr,
                                       target_ulong size, target_ulong pc,
                                       PtrTag ea_tag, int ea_base_reg,
                                       target_ulong ea_base_reg_val);

/* C API for libc-model bodies: check an access whose pointer lives in a
 * named register (no EA scratch involved). */
void provenance_model_check_access(CPUArchState *env, target_ulong addr,
                                   target_ulong size, target_ulong pc,
                                   int reg);

/* ---- Pending fault ---- */
/* Point the per-run pending fault at the shared-memory slot (called from
 * snapshot_init after the shared mmap exists). */
void provenance_set_shared_fault_ptr(PendingProvenanceFault *ptr);
PendingProvenanceFault *provenance_get_pending_fault(void);
void provenance_clear_pending_fault(void);
/* Returns true if a pending provenance fault should be exposed as a crash. */
bool provenance_finalize_fault(CPUArchState *env);
/* Emit the structured finding line exactly once (dual-record policy). */
bool provenance_report_pending_finding(void);
/* Returns a human-readable reason string for the pending fault. */
const char *provenance_fault_reason(void);

/* ---- snapshot_modify_memory hooks ---- */
void provenance_on_modify_reg(CPUArchState *env, int reg_idx);
void provenance_on_modify_mem(target_ulong addr, target_ulong size);

/* ---- Debug logging ---- */
extern int provenance_debug;

void provenance_log_tag(const char *ctx, int reg_idx, PtrTag tag);

#endif /* PROVENANCE_H */