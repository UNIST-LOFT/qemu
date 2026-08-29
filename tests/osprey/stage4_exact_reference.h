#ifndef BINRADAR_STAGE4_EXACT_REFERENCE_H
#define BINRADAR_STAGE4_EXACT_REFERENCE_H

#include "osprey-internal.h"

/* Test-only bounded slow oracle.  Rebuilds the primal graph, min-fill
 * elimination cliques, maximal cliques, and canonical maximum-weight clique
 * tree without calling production topology helpers. */
bool stage4_exact_reference_validate(const OspreyExactBase *base,
                                     const OspreyExactTopology *topology);

#define STAGE4_REFERENCE_MAX_VARS 12u

typedef struct Stage4ReferenceVariable {
    uint8_t kind;
    OspreyVarPayload payload;
} Stage4ReferenceVariable;

typedef struct Stage4ReferenceFactor {
    uint16_t rule;
    uint8_t stage;
    uint8_t potential_kind;
    uint16_t head_idx;
    uint8_t negative;
    uint8_t reserved;
    double probability;
    uint32_t num_vars;
    uint32_t vars[OSPREY_FACTOR_MAX_ARITY];
} Stage4ReferenceFactor;

typedef struct Stage4ReferenceProblem {
    const Stage4ReferenceVariable *variables;
    uint32_t variable_count;
    const Stage4ReferenceFactor *factors;
    uint32_t factor_count;
} Stage4ReferenceProblem;

typedef struct Stage4ReferenceSolution {
    double logz;
    double marginals[STAGE4_REFERENCE_MAX_VARS];
} Stage4ReferenceSolution;

/* Independent bounded numerical oracle.  It consumes a declarative graph,
 * enumerates the complete Boolean state space, and uses only the accepted
 * pure factor evaluator for factor semantics.  It intentionally does not
 * call production projection, topology, message, marginal, or log-sum code. */
OspreyStatus stage4_exact_reference_bruteforce(
    const Stage4ReferenceProblem *problem, Stage4ReferenceSolution *solution);

#endif
