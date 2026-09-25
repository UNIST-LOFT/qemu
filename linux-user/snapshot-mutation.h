#ifndef BINRADAR_SNAPSHOT_MUTATION_H
#define BINRADAR_SNAPSHOT_MUTATION_H

/*
 * Mutation-plan records shared by the coordinator in ``snapshot.c`` and the
 * symbolic boundary advisor in ``snapshot-mutation-symbolic.c``.
 *
 * These are parent-owned, fixed-layout values.  Expression and query identity
 * is always a scalar pool index or a raw pointer-difference cursor; no
 * ``Expr *`` or ``Query *`` crosses this boundary.  The advisor only reads
 * records; the coordinator owns every allocation and every published plan.
 */

#include "qemu/osdep.h"
#include "snapshot.h"
#include "osprey.h"
#include "../tcg/symbolic/symbolic-struct.h"

#include <stdint.h>

typedef enum SnapshotMutationKind {
    SNAPSHOT_MUTATION_BYTES = 0,
    SNAPSHOT_MUTATION_POINTER_NULL = 1,
    SNAPSHOT_MUTATION_POINTER_OOB = 2,
    SNAPSHOT_MUTATION_POINTER_FRESH = 3,
} SnapshotMutationKind;

typedef struct SnapshotMutationTarget {
    uint64_t extent;
    uint8_t *bytes;             /* owned; only valid for FRESH */
    /* Baseline target interval retained only for Stage 7.5's child
     * observation.  These are zero for fresh/null writes and are not part of
     * the solver/shared mutation ABI. */
    uint64_t resolved_raw;
    uint64_t resolved_end;
} SnapshotMutationTarget;

/* Parent-owned immutable mutation write.  Expression and query identity are
 * scalar pool indexes; the executor never dereferences either pool.  Every
 * byte used after enqueue is private plan ownership. */
typedef struct SnapshotMutationWrite {
    SnapshotMutationKind kind;
    target_ulong addr;
    uint32_t size;
    int64_t expr_index;
    int64_t query_index;
    uint8_t value[sizeof(target_ulong)];
    SnapshotMutationTarget target;
} SnapshotMutationWrite;

_Static_assert(sizeof(target_ulong) <= sizeof(((MutationCandidate *)0)->value),
               "target_ulong does not fit MutationCandidate value");

typedef enum SnapshotMutationLane {
    SNAPSHOT_MUTATION_LANE_PRIMITIVE = 0,
    SNAPSHOT_MUTATION_LANE_POINTER = 1,
    SNAPSHOT_MUTATION_LANE_ARGUMENT = 2,
} SnapshotMutationLane;

typedef enum SnapshotMutationSourceKind {
    SNAPSHOT_MUTATION_SOURCE_PRIMITIVE = 0,
    SNAPSHOT_MUTATION_SOURCE_POINTER = 1,
    SNAPSHOT_MUTATION_SOURCE_ARGUMENT_PRIMITIVE = 2,
    SNAPSHOT_MUTATION_SOURCE_ARGUMENT_POINTER = 3,
} SnapshotMutationSourceKind;

typedef enum SnapshotMutationSeedSemantics {
    SNAPSHOT_MUTATION_SEED_SNAPSHOT_STATE = 0,
    SNAPSHOT_MUTATION_SEED_OBSERVED_READ = 1,
} SnapshotMutationSeedSemantics;

/* Queue scheduling policy.  `EXISTING` publishes the staged plans in the
 * order the advisors produced them, which is the historical behavior and the
 * default; `RETAINED_FIRST` applies one stable partition so witness-capable
 * plans run first.  The policy is a permutation of the same finite plan set:
 * it never changes membership, contents, or source identity. */
typedef enum SnapshotMutationSchedule {
    SNAPSHOT_MUTATION_SCHEDULE_EXISTING = 0,
    SNAPSHOT_MUTATION_SCHEDULE_RETAINED_FIRST = 1,
} SnapshotMutationSchedule;

/* Mutation-family portfolio policy.  `REPLACEMENT` preserves the historical
 * contract: a surviving specialized family suppresses generic alternatives
 * for its primary source.  `MIXED` is the bounded P4c C1 experiment: generic
 * alternatives are also staged for primitive primaries with a surviving
 * symbolic-boundary family, then the three advisor streams are interleaved. */
typedef enum SnapshotMutationPortfolio {
    SNAPSHOT_MUTATION_PORTFOLIO_REPLACEMENT = 0,
    SNAPSHOT_MUTATION_PORTFOLIO_MIXED = 1,
} SnapshotMutationPortfolio;

/* Scalar-only identity for the one retained primitive load a plan may
 * diagnose.  The bytes are the plan's expected loaded value; event identity
 * and the baseline epoch are copied from its validated source entry. */
typedef struct SnapshotMutationReadWitnessDescriptor {
    uint64_t baseline_epoch;
    SnapshotMutationLane lane;
    uint64_t access_id;
    uintptr_t pc;
    target_ulong addr;
    uint32_t width;
    uint8_t expected_bytes[sizeof(target_ulong)];
    bool valid;
} SnapshotMutationReadWitnessDescriptor;

typedef struct SnapshotMutationPlan {
    uint32_t num_mods;
    uint32_t advisor_id;       /* 0 for generic plans */
    uint32_t source_ordinal;   /* meaningful only when source_valid */
    uint64_t family_id;
    uint64_t source_epoch;
    SnapshotMutationSourceKind source_kind;
    SnapshotMutationSeedSemantics seed_semantics;
    bool source_valid;
    bool family_valid;
    bool source_retained;
    bool read_witness_applicable;
    SnapshotMutationReadWitnessDescriptor read_witness;
    SnapshotMutationWrite *mods;
} SnapshotMutationPlan;

/* Source identity is the parent's baseline key; access IDs are lane-local. */
typedef struct SnapshotMutationSourceToken {
    uint64_t run_epoch;
    uint32_t source_ordinal;
} SnapshotMutationSourceToken;

/* How the finalized machine-width load root extends the retained memory
 * bytes.  Derived from the load's mem_op at finalization time, never
 * guessed from the expression shape.  SNAPSHOT_ROOT_* is the public spelling
 * in snapshot.h; SNAPSHOT_MUTATION_ROOT_* aliases it for the advisor. */
#define SNAPSHOT_MUTATION_ROOT_IDENTITY SNAPSHOT_ROOT_IDENTITY
#define SNAPSHOT_MUTATION_ROOT_ZEXT SNAPSHOT_ROOT_ZEXT
#define SNAPSHOT_MUTATION_ROOT_SEXT SNAPSHOT_ROOT_SEXT
typedef SnapshotRootExtension SnapshotMutationRootExtension;


typedef struct SnapshotMutationBaselineEntry {
    SnapshotMutationSourceToken token;
    SnapshotMutationLane lane;
    SnapshotMutationSourceKind source_kind;
    uint64_t access_id;
    uintptr_t pc;
    target_ulong addr;
    uint32_t size;
    bool eligible;
    bool typed_eligible;
    bool protected_addr;
    bool target_ref_valid;
    bool observed_read_valid;
    int64_t expr_index;
    int64_t query_index;
    /* Physical bytes the baseline child actually loaded.  Distinct from
     * planner_bytes, which keeps the current generic/OSPREY descriptor
     * semantics.  Copied from the retained access record only when the
     * record names the same epoch, lane, slot, and access id. */
    uint8_t observed_read_bytes[sizeof(target_ulong)];
    /* Extension the finalized load root applied to those bytes. */
    SnapshotMutationRootExtension root_extension;
    uint8_t planner_bytes[sizeof(target_ulong)];
    OspreyRuntimeChunkRef cell;
    OspreyRuntimeAddressRef target_ref;
} SnapshotMutationBaselineEntry;

typedef struct SnapshotMutationBaseline {
    uint64_t run_epoch;
    uint32_t entry_count;
    bool counts_valid;
    int64_t query_start;
    int64_t query_end;
    int64_t expr_start;
    int64_t expr_end;
    SnapshotMutationBaselineEntry *entries;
} SnapshotMutationBaseline;

typedef struct SnapshotMutationProposalWrite {
    SnapshotMutationSourceToken destination;
    SnapshotMutationKind kind;
    uint32_t size;
    uint8_t value[sizeof(target_ulong)];
    uint64_t target_extent;
    const uint8_t *target_bytes;
    uint64_t resolved_raw;
    uint64_t resolved_end;
} SnapshotMutationProposalWrite;

typedef struct SnapshotMutationProposalVariant {
    uint32_t variant_id;
    uint32_t write_count;
    SnapshotMutationProposalWrite *writes;
} SnapshotMutationProposalVariant;

typedef struct SnapshotMutationProposalFamily {
    uint32_t advisor_id;
    uint32_t advisor_priority;
    uint64_t family_id;
    SnapshotMutationSourceToken primary_seed;
    SnapshotMutationSeedSemantics seed_semantics;
    uint32_t variant_count;
    SnapshotMutationProposalVariant *variants;
} SnapshotMutationProposalFamily;

typedef struct SnapshotMutationCoordinator {
    const SnapshotMutationBaseline *baseline;
    GPtrArray *families; /* owns accepted family copies */
    GPtrArray *staged;   /* owns SnapshotMutationPlan values */
} SnapshotMutationCoordinator;

typedef struct SnapshotMutationProposalSink {
    SnapshotMutationCoordinator *coordinator;
    uint32_t advisor_id;
    uint32_t advisor_priority;
} SnapshotMutationProposalSink;

/* Destination eligibility for symbolic advice: the byte span must lie inside
 * snapshot-writable pages.  Defined in ``snapshot.c``; the advisor borrows it
 * so both paths accept exactly the same destinations. */
bool snapshot_mutation_writable_span(target_ulong addr, uint32_t size);

/* Validate and accept one proposal family through the ordinary coordinator
 * path.  Defined in ``snapshot.c``; the advisor submits through this so quota,
 * validation, and all-or-none staging semantics stay in one place.  Returns
 * false on any rejection (quota, validation, allocation), which the caller
 * treats as a local abstention. */
bool snapshot_mutation_sink_submit(SnapshotMutationProposalSink *sink,
                                   const SnapshotMutationProposalFamily *family);

#endif /* BINRADAR_SNAPSHOT_MUTATION_H */
