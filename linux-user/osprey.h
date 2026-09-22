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
/* Stage 7.1: fixed-layout runtime access locators                     */
/* ------------------------------------------------------------------ */

/* Fixed-layout, pointer-free locator for one runtime address: the
 * canonical identity (region + signed offset), the raw runtime address,
 * and the allocation-instance identity that made the canonical mapping
 * unique at capture time.  Lives inside SharedTraceData records, so the
 * layout must never change (shared mmap between parent and child).
 * valid == 0 means "no locator": the record stays generic-eligible. */
typedef struct OspreyRuntimeAddressRef {
    OspreyAddress address;
    uint64_t raw;             /* raw runtime guest address */
    uint64_t instance_id;     /* 0 for the merged global instance */
    uint64_t prov_object_id;  /* heap only; 0 otherwise */
    uint32_t prov_generation; /* heap only; 0 otherwise */
    uint8_t valid;
    uint8_t reserved[3];
} OspreyRuntimeAddressRef;

/* Fixed-layout locator for a contiguous access interval: the start
 * address locator plus the exact width.  A chunk is captured only when
 * every byte resolves into one allocation instance with consecutive
 * canonical offsets (same contract as osprey_chunk_of_interval). */
typedef struct OspreyRuntimeChunkRef {
    OspreyRuntimeAddressRef start;
    uint64_t size;
} OspreyRuntimeChunkRef;

/* ------------------------------------------------------------------ */
/* Configuration                                                       */
/* ------------------------------------------------------------------ */

typedef enum OspreyAnalysisMode {
    /* Zero preserves the direct-configuration contract used by the
     * research/unit callers.  Environment configuration explicitly selects
     * mutation mode by default; full mode is opt-in there. */
    OSPREY_ANALYSIS_MODE_FULL = 0,
    OSPREY_ANALYSIS_MODE_MUTATION = 1,
} OspreyAnalysisMode;

typedef enum OspreyMutationAggregateKind {
    OSPREY_MUTATION_AGGREGATE_ARRAY = 1,
    OSPREY_MUTATION_AGGREGATE_STRUCT = 2,
} OspreyMutationAggregateKind;

#define OSPREY_MUTATION_MAX_EXTENT UINT64_C(4096)

typedef struct OspreyConfig {
    bool enabled;
    uint8_t analysis_mode;      /* OspreyAnalysisMode */
    uint8_t reserved_mode[7];
    uint64_t shared_bytes;      /* BINRADAR_OSPREY_SHARED_MB * 1 MiB */
    uint64_t max_facts;         /* total unique facts per sample */
    uint64_t max_chunks_per_region;
    uint64_t max_candidates_per_kind_region;
    uint64_t max_variables;
    uint64_t max_factors;
    uint64_t max_exact_clique_vars;
    uint64_t max_exact_table_bytes; /* BINRADAR_OSPREY_MAX_EXACT_TABLE_MB * 1 MiB */
    uint64_t max_bp_table_bytes;    /* BINRADAR_OSPREY_MAX_BP_TABLE_MB * 1 MiB */
    /* Parent-only analysis limits; never copied into OspreySharedRun. */
    uint64_t max_analysis_work;     /* BINRADAR_OSPREY_MAX_ANALYSIS_WORK */
    uint64_t analysis_deadline_ms;  /* optional monotonic guard; 0 = off */
    uint64_t max_parent_facts;      /* BINRADAR_OSPREY_MAX_PARENT_FACTS */
    uint64_t max_parent_chunks;     /* BINRADAR_OSPREY_MAX_PARENT_CHUNKS */
    uint64_t max_parent_regions;    /* BINRADAR_OSPREY_MAX_PARENT_REGIONS */
    /* Mutation-mode limits.  Zero means unlimited for direct/unit callers;
     * environment configuration supplies bounded defaults. */
    uint64_t max_mutation_input;    /* BINRADAR_OSPREY_MAX_MUTATION_INPUT */
    uint64_t max_mutation_work;     /* BINRADAR_OSPREY_MAX_MUTATION_WORK */
    uint64_t max_mutation_bytes;    /* BINRADAR_OSPREY_MAX_MUTATION_BYTES */
    double report_threshold;
    char dump_file[512];        /* BINRADAR_OSPREY_DUMP_FILE: canonical
                                 * fact dump written after each
                                 * successful merge (empty = off) */
    char graph_dump_file[512];  /* BINRADAR_OSPREY_GRAPH_DUMP_FILE:
                                 * canonical Stage-3 graph dump (empty = off) */
    char model_dump_file[512];  /* BINRADAR_OSPREY_MODEL_DUMP_FILE:
                                 * validated canonical model (empty = off) */
} OspreyConfig;

/* ------------------------------------------------------------------ */
/* Public API                                                          */
/* ------------------------------------------------------------------ */

typedef struct OspreyContext OspreyContext;
typedef struct OspreySharedRun OspreySharedRun;
typedef struct OspreyModel OspreyModel;
typedef struct OspreyMutationModel OspreyMutationModel;

typedef enum OspreyStatus {
    OSPREY_OK = 0,
    OSPREY_DISABLED,
    OSPREY_INCOMPLETE_FACTS,
    OSPREY_LIMIT_EXCEEDED,
    OSPREY_EXACT_COMPONENT_TOO_LARGE,
    OSPREY_NON_CONVERGED,
    OSPREY_INVALID_MODEL,
    OSPREY_UNSUPPORTED_EXECUTION,
    OSPREY_RELATION_ARITHMETIC,
    OSPREY_INVALID_GRAPH,
    OSPREY_GRAPH_ARITHMETIC,
} OspreyStatus;

typedef struct OspreyDecodedObject {
    OspreyChunk chunk;
    uint8_t storage_role;       /* OspreyStorageRole */
    uint8_t has_pointer_target;
    uint16_t reserved;
    uint32_t value_type_id;     /* stable ordinal into model->types */
    OspreyAddress owner_base;   /* valid for field/array-element roles */
    OspreyAddress pointer_target; /* valid when has_pointer_target */
    double storage_posterior;
    double pointer_posterior;
    uint64_t storage_support;
    uint64_t storage_source_rule_bits;
    uint64_t pointer_support;
    uint64_t pointer_source_rule_bits;
} OspreyDecodedObject;

/* Stage 7.2: side-effect-free parent-side runtime resolution.  All
 * non-exact results are typed-unavailable and leave the model and mutation
 * queue untouched. */
typedef enum OspreyRuntimeResolveStatus {
    OSPREY_RUNTIME_RESOLVED = 0,
    OSPREY_RUNTIME_NO_LOCATOR,
    OSPREY_RUNTIME_INDEX_UNAVAILABLE,
    OSPREY_RUNTIME_NO_CELL_OBJECT,
    OSPREY_RUNTIME_NON_POINTER,
    OSPREY_RUNTIME_NO_POINTER_TARGET,
    OSPREY_RUNTIME_VOID_TARGET,
    OSPREY_RUNTIME_MISSING_TYPE,
    OSPREY_RUNTIME_MISSING_AGGREGATE,
    OSPREY_RUNTIME_STALE_INSTANCE,
    OSPREY_RUNTIME_AMBIGUOUS_INSTANCE,
    OSPREY_RUNTIME_OUT_OF_BOUNDS,
    OSPREY_RUNTIME_MALFORMED,
} OspreyRuntimeResolveStatus;

typedef struct OspreyRuntimeCellResolution {
    OspreyRuntimeResolveStatus status;
    uint32_t entry_ordinal;      /* UINT32_MAX unless status is RESOLVED */
    uint8_t instance_valid;      /* copied exact cell locator is valid */
    uint8_t aggregate_kind;      /* compact ARRAY or STRUCT evidence */
    uint8_t reserved[2];
    OspreyRuntimeChunkRef cell;
    OspreyAddress target_base;    /* exact compact target identity */
    uint64_t target_extent;       /* checked compact extent */
} OspreyRuntimeCellResolution;

typedef struct OspreyRuntimePointerResolution {
    OspreyRuntimeResolveStatus status;
    uint32_t entry_ordinal;      /* compact cell-entry ordinal */
    uint64_t target_extent;      /* compact checked aggregate extent */
    uint8_t aggregate_kind;      /* OspreyMutationAggregateKind */
    uint8_t has_runtime_target;  /* false for NULL -> fresh */
    uint8_t target_valid;
    uint8_t reserved;
    OspreyRuntimeCellResolution cell;
    OspreyAddress target_base;   /* selected canonical aggregate base */
    OspreyRuntimeAddressRef target;
} OspreyRuntimePointerResolution;

/* Compact runtime reception is checked once after B1 publication.  A failed
 * reception hides compact advice for the current transaction; resolvers do
 * not repeat structural model validation per access. */
bool osprey_runtime_mutation_prepare(OspreyContext *ctx);
const OspreyMutationModel *osprey_runtime_mutation_model(
    const OspreyContext *ctx);

/* Test-only counters prove one-time reception validation and logarithmic
 * cell/runtime searches without exposing production model internals. */
typedef struct OspreyRuntimeCounters {
    uint64_t reception_validation_passes;
    uint64_t cell_key_comparisons;
    uint64_t runtime_instance_comparisons;
} OspreyRuntimeCounters;
void osprey_runtime_test_reset_counters(void);
void osprey_runtime_test_get_counters(OspreyRuntimeCounters *out);

/* Read-only parent-side resolver over the immutable B1 compact model.  The
 * result is exact only when the returned status is RESOLVED; all other
 * statuses are typed-unavailable for the individual access. */
OspreyRuntimeResolveStatus osprey_runtime_resolve_cell(
    const OspreyContext *ctx, const OspreyMutationModel *model,
    const OspreyRuntimeChunkRef *locator,
    OspreyRuntimeCellResolution *out);
OspreyRuntimeResolveStatus osprey_runtime_resolve_pointer(
    const OspreyContext *ctx, const OspreyMutationModel *model,
    const OspreyRuntimeChunkRef *cell_locator, target_ulong concrete_value,
    const OspreyRuntimeAddressRef *target_locator,
    OspreyRuntimePointerResolution *out);

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

/* B1 facts-only mutation advisor.  The returned model is immutable and is
 * visible only after a successful compact transaction.  A rejected build
 * hides any prior allocation until the next successful publication. */
OspreyStatus osprey_mutation_model_build(OspreyContext *ctx);
const OspreyMutationModel *osprey_mutation_model(const OspreyContext *ctx);
void osprey_mutation_model_clear(OspreyContext *ctx);

/* Decoded-object lookup by canonical chunk. */
const OspreyDecodedObject *osprey_lookup_chunk(const OspreyModel *model,
                                                const OspreyChunk *chunk);

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

/* Ordered helper intervals remain private OSPREY origin state.  The semantic
 * event layer stages a complete family and commits it only after the helper's
 * architectural operation succeeds. */
typedef enum OspreyHelperIntervalResult {
    OSPREY_HELPER_INTERVAL_OK = 0,
    OSPREY_HELPER_INTERVAL_CONTRACT_MISMATCH,
    OSPREY_HELPER_INTERVAL_FULL,
} OspreyHelperIntervalResult;

void osprey_helper_intervals_reset(CPUArchState *env);
OspreyHelperIntervalResult osprey_helper_interval_stage(
    CPUArchState *env, target_ulong addr, target_ulong size, target_ulong pc,
    bool is_store, uint32_t op_class, uint32_t interval_policy,
    uint32_t producer_id);
void osprey_helper_intervals_commit(CPUArchState *env);

/* Semantic-event adapters own no OSPREY origin representation.  These calls
 * stage and consume the transient EA/producer-PC state around successful
 * architectural effects. */
void osprey_sem_ea_begin(CPUArchState *env, uint32_t base_reg,
                         uint32_t index_reg, uint32_t scale,
                         target_ulong disp, uint32_t mode, bool eligible);
void osprey_sem_ea_set_mode(CPUArchState *env, uint32_t mode, bool eligible);
void osprey_sem_ea_set_values(CPUArchState *env, target_ulong base_value,
                              target_ulong index_value);
uint32_t osprey_sem_ea_peek_mode(CPUArchState *env);
uint32_t osprey_sem_ea_take_mode(CPUArchState *env);
void osprey_sem_ea_clear(CPUArchState *env, bool clear_mode);
void osprey_sem_transfer_set(CPUArchState *env, target_ulong pc);
target_ulong osprey_sem_transfer_take(CPUArchState *env);
void osprey_sem_transfer_clear(CPUArchState *env);

/* ------------------------------------------------------------------ */
/* Allocator observation (Stage 2.5)                                   */
/* ------------------------------------------------------------------ */

typedef enum OspreyAllocatorKind {
    OSPREY_ALLOCATOR_MALLOC = 0,
    OSPREY_ALLOCATOR_CALLOC,
    OSPREY_ALLOCATOR_REALLOC,
} OspreyAllocatorKind;

/* One immutable process-local allocator observation.  Constructed at
 * the modeled return hook from the per-CPU pending operation; never
 * stored in shared memory and never pointing at child-owned state.
 * malloc/realloc carry zero element fields; calloc carries its original
 * concrete operands (even on failure) plus the checked total in
 * requested_size on success. */
typedef struct OspreyAllocatorObservation {
    OspreyAllocatorKind kind;
    target_ulong site_pc;         /* raw call PC (normalized here) */
    target_ulong requested_size;  /* checked total bytes */
    target_ulong element_count;   /* calloc only */
    target_ulong element_size;    /* calloc only */
    bool overflowed;              /* failed calloc product */
} OspreyAllocatorObservation;

/* Successful-return allocator hook.  Publishes the heap region
 * instance, F05, optional F06 (checked positive calloc geometry), and
 * the return ADDRESS origin only after the complete event validation
 * succeeds.  A failed/overflowed allocation creates no heap region and
 * no fact.  A successful zero-size return keeps a zero-size instance. */
void osprey_on_alloc_success(CPUArchState *env,
                             const OspreyAllocatorObservation *obs,
                             target_ulong base,
                             uint64_t object_id, uint32_t generation);
/* Failed allocator diagnostic only: emits a stable log row; never
 * touches shared fact state. */
void osprey_on_alloc_failure(const OspreyAllocatorObservation *obs);
/* Identity-based retire (provenance-authoritative heap lifecycle). */
void osprey_on_free_identity(CPUArchState *env, uint64_t object_id,
                             uint32_t generation, target_ulong site_pc);

/* Modeled byte-copy (memcpy/memmove/strcpy family) after the guest
 * access succeeded: source/destination are runtime addresses. */
void osprey_on_mem_copy(CPUArchState *env, target_ulong src,
                        target_ulong dst, target_ulong size);

/* OSPREY consumers of the shared semantic-event layer.  Stage 2.2
 * centralizes dispatch; Stages 2.3–2.4 complete address/value policy.
 * Every accepted Stage 2.3 transfer event carries the raw instruction
 * PC so the origin's producer identity is exact and image-relative. */
void osprey_on_reg_materialize_address(CPUArchState *env, uint32_t dst,
                                       target_ulong value,
                                       target_ulong pc);
void osprey_on_reg_copy(CPUArchState *env, uint32_t dst, uint32_t src,
                        target_ulong src_value, target_ulong dst_value,
                        target_ulong pc);
void osprey_on_reg_lea(CPUArchState *env, uint32_t dst, uint32_t base,
                       int64_t disp, target_ulong dst_value,
                       target_ulong base_value, target_ulong pc);
void osprey_on_reg_addsub_imm(CPUArchState *env, uint32_t reg,
                              int64_t delta, target_ulong pre_value,
                              target_ulong post_value, target_ulong pc);
void osprey_on_reg_addsub_reg(CPUArchState *env, uint32_t dst,
                              uint32_t src, bool is_sub,
                              target_ulong dst_value,
                              target_ulong src_value, target_ulong pc);
void osprey_on_reg_xchg(CPUArchState *env, uint32_t dst, uint32_t src,
                        target_ulong dst_value, target_ulong src_value,
                        target_ulong pc);
void osprey_on_reg_invalidate(CPUArchState *env, uint32_t reg);
/* Combined Stage 2.4 memory hooks (replaces the Stage 2.3
 * osprey_on_mem_{load,store}_address split).  Both run only after a
 * successful guest access.  On load, the helper reads the post-load
 * architectural GPR value from env->regs[dst] itself; on store the
 * source register index, address, size, and src_value are explicit.
 * Each hook clears/updates the destination channels, invalidates
 * overlap, then evaluates the applicable facts (F02, F03, F04) and
 * shadow installation. */
void osprey_on_mem_load(CPUArchState *env, uint32_t dst,
                        target_ulong addr, target_ulong size,
                        uint64_t pc);
void osprey_on_mem_store(CPUArchState *env, uint32_t src,
                         target_ulong addr, target_ulong size,
                         target_ulong src_value, target_ulong pc);
/* External/unknown-source overwrite: exact overlap invalidation only,
 * no fact or replacement metadata. */
void osprey_on_mem_overwrite(CPUArchState *env, target_ulong addr,
                             target_ulong size);

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
