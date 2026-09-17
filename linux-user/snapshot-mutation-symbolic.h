#ifndef BINRADAR_SNAPSHOT_MUTATION_SYMBOLIC_H
#define BINRADAR_SNAPSHOT_MUTATION_SYMBOLIC_H

/*
 * Bounded comparison-guided scalar mutation advisor.
 *
 * This is not a solver.  It binds a retained read to its final machine-width
 * load root and admitted concretization query, propagates an exact single
 * source label forward through a small invertible expression grammar, finds
 * the branch comparisons that consume those labels, and proposes the nearest
 * value on the opposite side of the observed branch.  Everything it cannot
 * prove exactly is a local abstention.
 *
 * The advisor runs once, synchronously, in the forkserver parent after the
 * baseline child exits.  It borrows the frozen expression and query pools for
 * the duration of the call and owns nothing afterwards; accepted candidates
 * are submitted through the ordinary proposal sink, which copies every value.
 */

#include "snapshot-mutation.h"

typedef enum SnapshotSymbolicMode {
    SNAPSHOT_SYMBOLIC_OFF = 0,      /* no capture consumption, no proposals */
    SNAPSHOT_SYMBOLIC_SHADOW = 1,   /* rank and report, submit nothing */
    SNAPSHOT_SYMBOLIC_BOUNDARY = 2, /* submit advisor-ID-2 families */
} SnapshotSymbolicMode;

/* Immutable read-only view of the frozen pools and the validated baseline.
 * Every index is a half-open raw pointer-difference cursor into its pool. */
typedef struct SnapshotSymbolicView {
    const Expr *expr_base;
    const Query *query_base;
    int64_t expr_entry;
    int64_t expr_exit;
    int64_t query_entry;
    int64_t query_exit;
    const SnapshotMutationBaseline *baseline;
    uint64_t run_epoch;
} SnapshotSymbolicView;

/* Advisor identity reserved for symbolic boundary advice.  Compact OSPREY owns
 * advisor ID 1 and priority 0; the coordinator applies per-advisor quotas. */
#define SNAPSHOT_SYMBOLIC_ADVISOR_ID 2u
#define SNAPSHOT_SYMBOLIC_ADVISOR_PRIORITY 1u

/* Candidate ceiling per source, matching the generic primitive path. */
#define SNAPSHOT_SYMBOLIC_MAX_CANDIDATES_PER_SOURCE 3u

/* Parse and validate the BinRadar-only advisor configuration.  Safe to call
 * before snapshot_init(); a parse failure disables the advisor. */
void snapshot_symbolic_configure(void);

SnapshotSymbolicMode snapshot_symbolic_mode(void);

/* Run the advisor once.  view and sink must be non-NULL; sink is only used in
 * boundary mode.  Returns the number of accepted families (0 in shadow mode).
 * Never fails destructively: every error path is a local abstention. */
uint32_t snapshot_symbolic_run(const SnapshotSymbolicView *view,
                               SnapshotMutationProposalSink *sink);

#endif /* BINRADAR_SNAPSHOT_MUTATION_SYMBOLIC_H */
