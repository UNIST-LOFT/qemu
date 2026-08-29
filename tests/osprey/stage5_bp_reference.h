#ifndef STAGE5_BP_REFERENCE_H
#define STAGE5_BP_REFERENCE_H

#include "osprey.h"
#include "osprey-internal.h"

/* Independent declarative ownership check for bounded Stage 5.1 graphs. */
bool stage5_bp_reference_matches(const OspreyContext *ctx,
                                 const OspreyBpGraph *graph);

#endif
