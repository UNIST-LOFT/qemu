#ifndef BINRADAR_OSPREY_H
#define BINRADAR_OSPREY_H

/*
 * OSPREY in-process structural type analysis for the binradar tracer.
 *
 * This is a C reimplementation of the corrected OSPREY reference
 * (agent-docs/info/OSPREY_TYPE_INFERENCE/OSPREY_IMPLEMENTATION.md),
 * replacing the external Python analyzer (fuzzolic/analyze_type.py) with
 * fact collection inside the tracer, deterministic closure, factor-graph
 * inference, and consistent decoding.
 *
 * Ownership model (see OSPREY_IMPLEMENTATION_PLAN.md §6):
 *  - The forkserver parent owns the OspreyContext, committed facts, graph
 *    state, and OspreyModel.
 *  - Each baseline child writes only fixed-layout fact/support records
 *    and sticky overflow flags into a shared MAP_SHARED OspreySharedRun;
 *    it never publishes GLib pointers.
 *  - The parent merges the shared run after the child exits and runs
 *    inference at the patch-0/iter-1 barrier.
 */

#include "qemu/osdep.h"

#include <stdint.h>

/* Include the CPU state definition (CPUArchState, CPU_NB_REGS) exactly
 * like linux-user/snapshot.h does. */
#include "qemu.h"

/* ------------------------------------------------------------------ */
/* Canonical memory model                                              */
/* ------------------------------------------------------------------ */

typedef enum OspreyRegionKind {
    OSPREY_REGION_GLOBAL = 0,       /* G:  main executable writable data */
    OSPREY_REGION_HEAP_SITE = 1,    /* H_i: allocation site i */
    OSPREY_REGION_STACK_FUNCTION = 2, /* S_f: callee function f */
} OspreyRegionKind;

/* Canonical region identity.  code_image_id == 0 is the main executable
 * in the first implementation; PCs and global addresses are normalized
 * against the main image base (symbolic_start_code), so PIE/ASLR changes
 * do not change abstract identity. */
typedef struct OspreyRegionId {
    OspreyRegionKind kind;
    uint64_t code_image_id;
    uint64_t site_offset; /* image-relative normalized offset */
} OspreyRegionId;

typedef struct OspreyAddress {
    OspreyRegionId region;
    int64_t offset; /* signed; stack offsets are relative to entry SP */
} OspreyAddress;

typedef struct OspreyChunk {
    OspreyAddress address;
    uint64_t size; /* access width; overlapping widths coexist */
} OspreyChunk;

/* ------------------------------------------------------------------ */
/* Configuration                                                       */
/* ------------------------------------------------------------------ */

typedef struct OspreyConfig {
    bool enabled;
    uint64_t shared_bytes;      /* BINRADAR_OSPREY_SHARED_MB * 1 MiB */
    uint64_t max_facts;         /* total unique facts per sample */
    uint64_t max_chunks_per_region;
    uint64_t max_candidates_per_kind_region;
    uint64_t max_variables;
    uint64_t max_factors;
    uint64_t max_exact_clique_vars;
    double report_threshold;
    char dump_file[512];        /* BINRADAR_OSPREY_DUMP_FILE: canonical
                                 * fact dump written after each
                                 * successful merge (empty = off) */
} OspreyConfig;

/* ------------------------------------------------------------------ */
/* Public API                                                          */
/* ------------------------------------------------------------------ */

typedef struct OspreyContext OspreyContext;
typedef struct OspreySharedRun OspreySharedRun;
typedef struct OspreyModel OspreyModel;

typedef enum OspreyStatus {
    OSPREY_OK = 0,
    OSPREY_DISABLED,
    OSPREY_INCOMPLETE_FACTS,
    OSPREY_LIMIT_EXCEEDED,
    OSPREY_EXACT_COMPONENT_TOO_LARGE,
    OSPREY_NON_CONVERGED,
    OSPREY_INVALID_MODEL,
    OSPREY_UNSUPPORTED_EXECUTION,
} OspreyStatus;

typedef struct OspreyDecodedObject {
    OspreyChunk chunk;
    uint64_t kind;      /* OspreyDecodedKind (see osprey-internal.h) */
    double posterior;
    int64_t parent_offset; /* structure base / array start offset */
    OspreyRegionId parent_region;
    uint32_t type_id;   /* stable ordinal into the model type table */
} OspreyDecodedObject;

/* Configuration: parse + validate all BINRADAR_OSPREY_* env vars once.
 * Returns false (and logs the offending variable/value) on invalid or
 * overflowing input; callers must fail tracer startup then. */
bool osprey_config_from_env(OspreyConfig *config);

OspreyContext *osprey_new(const OspreyConfig *config);
void osprey_free(OspreyContext *ctx);

/* Size of the shared per-run fact transport (fixed layout, no pointers). */
size_t osprey_shared_run_size(const OspreyConfig *config);
void osprey_shared_run_reset(OspreySharedRun *run, uint64_t sample_id,
                             const OspreyConfig *config);

/* Child side: attach the shared sink for fact collection. */
void osprey_child_use_shared_run(OspreyContext *ctx, OspreySharedRun *run);

/* Stage 2.1 sample composition: freeze the pre-snapshot prefix so a
 * baseline sample is `prefix ∪ baseline-child` as exactly one
 * unmodified sample.  Called at snapshot_save() (before the baseline
 * fork): the current shared-run contents are copied into the run's
 * prefix record; later child hooks keep writing to the tables.  The
 * parent merges the union at osprey_parent_merge_sample(); a fact
 * present in both parts has sample_support 1, never 2. */
bool osprey_shared_run_freeze_prefix(OspreyContext *ctx,
                                     OspreySharedRun *run);
/* Baseline forkserver path: reset the per-child suffix only, keeping
 * the frozen prefix intact so the child inherits exactly the
 * pre-snapshot facts.  Falls back to a full reset when no prefix is
 * frozen. */
void osprey_shared_run_prepare(OspreyContext *ctx, OspreySharedRun *run,
                               uint64_t sample_id);

/* Parent side: merge one completed sample (prefix + child) into the
 * committed fact tables. */
OspreyStatus osprey_parent_merge_sample(OspreyContext *ctx,
                                         const OspreySharedRun *run);

/* Run deterministic closure, inference, and decoding. */
OspreyStatus osprey_analyze(OspreyContext *ctx);

/* The model usable by consumers: NULL unless the committed analysis
 * transaction is OSPREY_OK.  Fail-closed: a rejected transaction never
 * exposes a model, not even a previously installed one. */
const OspreyModel *osprey_model(const OspreyContext *ctx);

/* Decoded-object lookup by canonical chunk. */
const OspreyDecodedObject *osprey_lookup_chunk(const OspreyModel *model,
                                                const OspreyChunk *chunk);

/* Stage 7 consumer API (parent side): map a raw guest address back to
 * the decoded object covering it (chunk-exact for scalar/field/pointer
 * chunks; point base for array starts).  Returns NULL when the address
 * is outside every modeled instance. */
const OspreyDecodedObject *osprey_lookup_raw(const OspreyModel *model,
                                              uint64_t raw);

/* Raw extent of a decoded object's canonical span: for struct/array
 * bases the merged region-instance extent; for chunks their size.
 * Returns false when no instance resolves. */
bool osprey_raw_extent(const OspreyModel *model,
                       const OspreyDecodedObject *obj, uint64_t *raw_out,
                       uint64_t *extent_out);

/* ------------------------------------------------------------------ */
/* Runtime collection hooks (called from translated code / models)     */
/* ------------------------------------------------------------------ */

/* EA metadata consumption (Stage 2.2): the shared semantic-event layer
 * (linux-user/sem-events.c) records the EA record before the guest
 * access; this hook runs AFTER the access succeeds and consumes that
 * metadata.  A faulting access therefore never records facts. */
void osprey_on_mem_access(CPUArchState *env, target_ulong addr,
                          uint64_t size, uint64_t pc, uint32_t is_store);
void osprey_on_mem_access_class(CPUArchState *env, target_ulong addr,
                                uint64_t size, uint64_t pc,
                                uint32_t is_store, uint32_t op_class);

/* Successful-return allocator hooks (site = call PC of the allocator).
 * A failed/overflowed allocation creates no heap region and no size
 * fact.  A successful zero-size return keeps a zero-size instance. */
void osprey_on_alloc_success(CPUArchState *env, target_ulong base,
                             target_ulong size, target_ulong site_pc,
                             uint64_t object_id, uint32_t generation);
void osprey_on_alloc_failure(CPUArchState *env, target_ulong site_pc);
/* Identity-based retire (provenance-authoritative heap lifecycle). */
void osprey_on_free_identity(CPUArchState *env, uint64_t object_id,
                             uint32_t generation, target_ulong site_pc);

/* Modeled byte-copy (memcpy/memmove/strcpy family) after the guest
 * access succeeded: source/destination are runtime addresses. */
void osprey_on_mem_copy(CPUArchState *env, target_ulong src,
                        target_ulong dst, target_ulong size);

/* OSPREY consumers of the shared semantic-event layer.  Stage 2.2
 * centralizes dispatch; Stages 2.3–2.4 complete address/value policy. */
void osprey_on_reg_copy(CPUArchState *env, uint32_t dst, uint32_t src,
                        target_ulong src_val, target_ulong dst_val);
void osprey_on_reg_lea(CPUArchState *env, uint32_t dst, uint32_t base,
                       int64_t disp, target_ulong dst_val,
                       target_ulong base_val);
void osprey_on_reg_invalidate(CPUArchState *env, uint32_t reg);
void osprey_on_mem_store_origin(CPUArchState *env, uint32_t src_reg,
                                target_ulong addr, target_ulong size,
                                target_ulong src_val);
void osprey_on_mem_load_origin(CPUArchState *env, uint32_t dst_reg,
                               target_ulong addr, target_ulong value);

/* Call/return stack events.  The call hook fires AFTER the return-
 * address push, so entry_sp is the precise callee-entry RSP; callee_pc
 * is the runtime callee entry (out-of-image callees are flagged
 * imprecise and never contribute facts).  The ret hook fires after the
 * pop (post-pop RSP). */
void osprey_on_call(CPUArchState *env, target_ulong callee_pc,
                    target_ulong entry_sp);
void osprey_on_ret(CPUArchState *env, target_ulong pc, target_ulong sp);
/* RSP write (push/pop/add-sub imm): re-derive the RSP origin from the
 * live frame stack; only in-image writes re-derive. */
void osprey_on_rsp_update(CPUArchState *env, target_ulong new_sp,
                          target_ulong pc);

/* Entrypoint barrier (snapshot/forkserver entry): seed the initial
 * stack frame for the main image when the entrypoint is reached from
 * uninstrumented loader/libc code (no call hook fired for main).
 * Idempotent: creates a precise frame only when no live frame with the
 * same region and entry SP exists; the observed entry SP is the
 * offset-zero anchor.  Fires once per process (parent at the target
 * hit; the child re-executes the entrypoint TB with count target+1). */
void osprey_on_entrypoint(CPUArchState *env, target_ulong pc,
                          target_ulong sp);

/* Mark the current sample unsupported (CLONE_VM multithreaded guest). */
void osprey_mark_unsupported_execution(void);

/* Collection enable flag (snapshot.c); read by the translator wrappers. */
extern int osprey_collect_enabled;

/* Main-image writable data ranges (registered from elfload.c). */
void osprey_register_image_global(CPUArchState *env, target_ulong base,
                                  target_ulong size);
/* Main image normalization base (== symbolic_load_base). */
void osprey_set_image_base(target_ulong base);
/* Final executable text interval, registered after all main-image LOAD
 * segments have been processed. */
void osprey_set_image_bounds(target_ulong start, target_ulong end);

/* Canonical fact dump (osprey-facts.c): deterministic sorted dump of
 * the merged facts, used for ASLR-invariance comparison. */
void osprey_dump_canonical(OspreyContext *ctx, const char *path);

#endif /* BINRADAR_OSPREY_H */
