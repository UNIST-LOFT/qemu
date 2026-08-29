#ifndef BINRADAR_STAGE4_EXACT_REFERENCE_H
#define BINRADAR_STAGE4_EXACT_REFERENCE_H

#include "osprey-internal.h"

/* Test-only bounded slow oracle.  Rebuilds the primal graph, min-fill
 * elimination cliques, maximal cliques, and canonical maximum-weight clique
 * tree without calling production topology helpers. */
bool stage4_exact_reference_validate(const OspreyExactBase *base,
                                     const OspreyExactTopology *topology);

#endif
