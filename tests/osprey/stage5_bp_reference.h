#ifndef STAGE5_BP_REFERENCE_H
#define STAGE5_BP_REFERENCE_H

#include "osprey.h"
#include "osprey-internal.h"

/* Independent declarative ownership check for bounded Stage 5.1 graphs. */
bool stage5_bp_reference_matches(const OspreyContext *ctx,
                                 const OspreyBpGraph *graph);

/* Independent one-round sum-product oracle.  It scans the declarative
 * factor graph rather than using production CSR adjacency or arithmetic. */
OspreyStatus stage5_bp_reference_compute_round(
    const OspreyContext *ctx, const OspreyBpGraph *graph,
    OspreyBpMessages *messages);

/* Independent factor half-step over an already completed variable-message
 * family.  Stage 5.3 uses this to verify that factor updates consume the
 * damped, rather than raw, variable half-step. */
OspreyStatus stage5_bp_reference_compute_factor_half(
    const OspreyContext *ctx, const OspreyBpGraph *graph,
    const double *vf_messages, double *fv_messages);

/* Independent bounded Stage 5.5 closure description.  The oracle uses direct
 * checked arithmetic and declarative semantic factor signatures; it does not
 * call production closure, candidate, BP, migration, or log helpers. */
typedef struct Stage5BpClosureCase {
    OspreyRegionId region;
    int64_t source_offset;
    uint64_t width;
    uint64_t prefix_size;
    uint64_t fold_size;
    uint64_t extent;
    double primitive_probability;
    double prefix_probability;
    double fold_probability;
    bool folded_preexisting;
} Stage5BpClosureCase;

bool stage5_bp_reference_closure_eligible(
    const Stage5BpClosureCase *description, int64_t *folded_offset_out);
bool stage5_bp_reference_closure_matches(
    const OspreyContext *ctx, const Stage5BpClosureCase *description);

#endif
