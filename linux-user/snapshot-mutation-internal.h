#ifndef BINRADAR_SNAPSHOT_MUTATION_INTERNAL_H
#define BINRADAR_SNAPSHOT_MUTATION_INTERNAL_H

#include "snapshot-mutation.h"

/* Internal owner API used by snapshot lifecycle code and the focused Stage-7
 * harness.  The public advisor contract remains in snapshot-mutation.h. */
void snapshot_mutation_test_set_alloc_fail_after(int64_t fail_after);
void *snapshot_mutation_try_malloc(size_t size);
void *snapshot_mutation_try_malloc0(size_t size);

typedef struct SnapshotMutationApplyHost {
    bool (*read_cell)(void *opaque, target_ulong addr, uint32_t size,
                      target_ulong *value_out);
    target_ulong (*allocate_target)(void *opaque, uint64_t extent);
    bool (*initialize_target)(void *opaque, target_ulong target,
                              const uint8_t *bytes, uint64_t extent);
    /* Called only after every destination and fresh target was validated.
     * Implementations must be infallible so a multiwrite plan cannot expose a
     * prefix and then report failure without rollback. */
    void (*publish_cell)(void *opaque, const SnapshotMutationWrite *write,
                         const uint8_t *value);
    void (*observe_write)(void *opaque, const SnapshotMutationWrite *write,
                          target_ulong fresh_target,
                          target_ulong before_value, bool applied);
} SnapshotMutationApplyHost;

typedef enum SnapshotMutationApplyResult {
    SNAPSHOT_MUTATION_APPLY_OK = 0,
    SNAPSHOT_MUTATION_APPLY_EMPTY,
    SNAPSHOT_MUTATION_APPLY_ALLOCATION,
    SNAPSHOT_MUTATION_APPLY_KIND,
    SNAPSHOT_MUTATION_APPLY_WIDTH,
    SNAPSHOT_MUTATION_APPLY_TARGET,
    SNAPSHOT_MUTATION_APPLY_REGISTER,
    SNAPSHOT_MUTATION_APPLY_DUPLICATE_REGISTER,
    SNAPSHOT_MUTATION_APPLY_DESTINATION,
    SNAPSHOT_MUTATION_APPLY_OVERLAP,
    SNAPSHOT_MUTATION_APPLY_FRESH_TARGET,
} SnapshotMutationApplyResult;

SnapshotMutationApplyResult snapshot_mutation_apply(
    const SnapshotMutationPlan *plan, const SnapshotMutationApplyHost *host,
    void *opaque);

void snapshot_mutation_free(SnapshotMutationPlan *plan);
void snapshot_mutation_free_batch(SnapshotMutationPlan **plans, size_t count);
SnapshotMutationPlan *snapshot_mutation_new_descriptor(
    target_ulong addr, uint32_t size, int64_t expr_index,
    int64_t query_index, SnapshotMutationKind kind, const uint8_t *value,
    uint64_t target_extent, const uint8_t *target_bytes);
bool snapshot_mutation_enqueue_batch(GQueue *queue,
                                     SnapshotMutationPlan **plans,
                                     uint32_t count);
bool snapshot_mutation_enqueue_one(GQueue *queue,
                                   SnapshotMutationPlan *plan);

const SnapshotMutationBaselineEntry *snapshot_mutation_lookup_entry(
    const SnapshotMutationBaseline *baseline,
    SnapshotMutationSourceToken token);
void snapshot_mutation_plan_set_source(
    SnapshotMutationPlan *plan, const SnapshotMutationBaseline *baseline,
    SnapshotMutationSourceToken primary,
    SnapshotMutationSeedSemantics seed_semantics, bool family_valid,
    uint64_t family_id);
void snapshot_mutation_proposal_family_free(gpointer data);
bool snapshot_mutation_proposal_validate(
    const SnapshotMutationCoordinator *coordinator,
    const SnapshotMutationProposalFamily *family);
void snapshot_mutation_baseline_free(SnapshotMutationBaseline *baseline);

bool snapshot_mutation_coordinator_init(
    SnapshotMutationCoordinator *coordinator,
    const SnapshotMutationBaseline *baseline);
void snapshot_mutation_coordinator_sort(
    SnapshotMutationCoordinator *coordinator);
bool snapshot_mutation_stage_family(
    SnapshotMutationCoordinator *coordinator,
    const SnapshotMutationProposalFamily *family);
bool snapshot_mutation_coordinator_publish(
    SnapshotMutationCoordinator *coordinator, GQueue *queue);

typedef struct SnapshotMutationPortfolioStats {
    uint64_t staged_input;
    uint64_t staged_output;
    uint64_t osprey_plans;
    uint64_t boundary_plans;
    uint64_t generic_plans;
    uint64_t suppressed_duplicates;
    bool allocation_failure;
} SnapshotMutationPortfolioStats;

SnapshotMutationPortfolio snapshot_mutation_portfolio_parse(
    const char *text, bool *valid_out);
/* `REPLACEMENT` is allocation-free and leaves `staged` byte-for-byte ordered.
 * `MIXED` atomically replaces it with a stable OSPREY/boundary/generic
 * round-robin, suppressing exact duplicate complete write sets. */
bool snapshot_mutation_coordinator_portfolio(
    SnapshotMutationCoordinator *coordinator,
    SnapshotMutationPortfolio portfolio,
    SnapshotMutationPortfolioStats *stats_out);

#define SNAPSHOT_MUTATION_SCHEDULE_DIGEST_LANES 8u
#define SNAPSHOT_MUTATION_SCHEDULE_DIGEST_HEX_LEN \
    (SNAPSHOT_MUTATION_SCHEDULE_DIGEST_LANES * 16u)

/* Counts and the pre-policy queue identities for the one `[binradar]
 * [schedule]` row.  `witness_capable` is the priority class size and `moved`
 * the number of plans the partition actually relocated.  `plan_content_digest`
 * hashes reproducible plan semantics and is the paired-trial equality key;
 * `cursor_fingerprint` separately reports run-local symbolic/event positions
 * that must never reject an otherwise matched pair. */
typedef struct SnapshotMutationScheduleStats {
    uint64_t staged;
    uint64_t witness_capable;
    uint64_t moved;
    uint64_t plan_content_digest[SNAPSHOT_MUTATION_SCHEDULE_DIGEST_LANES];
    uint64_t cursor_fingerprint[SNAPSHOT_MUTATION_SCHEDULE_DIGEST_LANES];
    bool allocation_failure;
} SnapshotMutationScheduleStats;

/* Parse `existing`, `retained-first`, or nothing at all (the default).
 * Any other text leaves *valid_out false and the caller keeps `existing`
 * rather than guessing which policy was requested. */
SnapshotMutationSchedule snapshot_mutation_schedule_parse(
    const char *text, bool *valid_out);

/* Stable-partition the staged array for the selected policy.  `existing`
 * leaves the array untouched, so the default publication order is unchanged. */
void snapshot_mutation_coordinator_schedule(
    SnapshotMutationCoordinator *coordinator,
    SnapshotMutationSchedule schedule,
    SnapshotMutationScheduleStats *stats_out);
void snapshot_mutation_coordinator_clear(
    SnapshotMutationCoordinator *coordinator);

#endif /* BINRADAR_SNAPSHOT_MUTATION_INTERNAL_H */
