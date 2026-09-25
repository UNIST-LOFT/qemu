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
void snapshot_mutation_coordinator_clear(
    SnapshotMutationCoordinator *coordinator);

#endif /* BINRADAR_SNAPSHOT_MUTATION_INTERNAL_H */
