#include "stage4_exact_reference.h"

#include <limits.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>

#define REF_MAX_VARS 16u
#define REF_MAX_TREE_EDGES 20u

typedef struct RefClique {
    uint32_t count;
    uint32_t vars[REF_MAX_VARS];
} RefClique;

typedef struct RefTreeCandidate {
    uint32_t left;
    uint32_t right;
    uint32_t weight;
} RefTreeCandidate;

static int ref_u32_compare(const void *ap, const void *bp)
{
    uint32_t a = *(const uint32_t *)ap;
    uint32_t b = *(const uint32_t *)bp;
    return a < b ? -1 : a != b;
}

static int ref_clique_compare(const void *ap, const void *bp)
{
    const RefClique *a = ap;
    const RefClique *b = bp;
    uint32_t common = a->count < b->count ? a->count : b->count;
    for (uint32_t i = 0; i < common; i++) {
        if (a->vars[i] != b->vars[i]) {
            return a->vars[i] < b->vars[i] ? -1 : 1;
        }
    }
    return a->count < b->count ? -1 : a->count != b->count;
}

static int ref_tree_candidate_compare(const void *ap, const void *bp)
{
    const RefTreeCandidate *a = ap;
    const RefTreeCandidate *b = bp;
    if (a->weight != b->weight) return a->weight > b->weight ? -1 : 1;
    if (a->left != b->left) return a->left < b->left ? -1 : 1;
    return a->right < b->right ? -1 : a->right != b->right;
}

static bool ref_clique_equal(const RefClique *a, const RefClique *b)
{
    return a->count == b->count &&
           memcmp(a->vars, b->vars, a->count * sizeof(a->vars[0])) == 0;
}

static bool ref_clique_strict_subset(const RefClique *small,
                                     const RefClique *large)
{
    uint32_t i = 0;
    uint32_t j = 0;
    if (small->count >= large->count) return false;
    while (i < small->count && j < large->count) {
        if (small->vars[i] == large->vars[j]) {
            i++;
            j++;
        } else if (small->vars[i] > large->vars[j]) {
            j++;
        } else {
            return false;
        }
    }
    return i == small->count;
}

static bool ref_actual_clique_equal(const RefClique *expected,
                                    const OspreyExactClique *actual)
{
    if (actual == NULL || actual->local_vars == NULL ||
        actual->local_vars->len != expected->count) {
        return false;
    }
    for (uint32_t i = 0; i < expected->count; i++) {
        if (g_array_index(actual->local_vars, uint32_t, i) !=
            expected->vars[i]) {
            return false;
        }
    }
    return true;
}

static bool ref_local_position(const OspreyExactComponent *component,
                               uint32_t local, uint32_t *position)
{
    if (component == NULL || component->local_vars == NULL ||
        position == NULL) {
        return false;
    }
    for (guint i = 0; i < component->local_vars->len; i++) {
        if (g_array_index(component->local_vars, uint32_t, i) == local) {
            *position = i;
            return true;
        }
    }
    return false;
}

static uint32_t ref_uf_find(uint32_t *parent, uint32_t value)
{
    while (parent[value] != value) {
        parent[value] = parent[parent[value]];
        value = parent[value];
    }
    return value;
}

static void ref_uf_union(uint32_t *parent, uint32_t a, uint32_t b)
{
    uint32_t ra = ref_uf_find(parent, a);
    uint32_t rb = ref_uf_find(parent, b);
    if (ra != rb) parent[rb] = ra;
}

static uint32_t ref_intersection_size(const RefClique *a, const RefClique *b)
{
    uint32_t i = 0;
    uint32_t j = 0;
    uint32_t count = 0;
    while (i < a->count && j < b->count) {
        if (a->vars[i] == b->vars[j]) {
            count++;
            i++;
            j++;
        } else if (a->vars[i] < b->vars[j]) {
            i++;
        } else {
            j++;
        }
    }
    return count;
}

static bool ref_tree_mask_preferred(uint64_t candidate, uint64_t current,
                                    uint32_t edge_count)
{
    for (uint32_t i = 0; i < edge_count; i++) {
        bool a = (candidate & (UINT64_C(1) << i)) != 0;
        bool b = (current & (UINT64_C(1) << i)) != 0;
        if (a != b) return a;
    }
    return false;
}

static bool ref_best_tree(const RefClique *cliques, uint32_t clique_count,
                          const OspreyExactTopologyComponent *actual)
{
    RefTreeCandidate candidates[REF_MAX_TREE_EDGES];
    uint32_t candidate_count = 0;
    uint64_t best_weight = 0;
    uint64_t best_mask = 0;
    bool found = false;

    if (clique_count == 1) return actual->tree_edges->len == 0;
    for (uint32_t left = 0; left < clique_count; left++) {
        for (uint32_t right = left + 1; right < clique_count; right++) {
            uint32_t weight = ref_intersection_size(&cliques[left],
                                                    &cliques[right]);
            if (weight == 0) continue;
            if (candidate_count == REF_MAX_TREE_EDGES) return false;
            candidates[candidate_count++] = (RefTreeCandidate) {
                left, right, weight
            };
        }
    }
    qsort(candidates, candidate_count, sizeof(candidates[0]),
          ref_tree_candidate_compare);
    if (candidate_count >= 63 || actual->tree_edges->len + 1 != clique_count) {
        return false;
    }

    uint64_t limit = UINT64_C(1) << candidate_count;
    for (uint64_t mask = 0; mask < limit; mask++) {
        if ((uint32_t)__builtin_popcountll(mask) != clique_count - 1) continue;
        uint32_t parent[REF_MAX_VARS];
        uint64_t weight = 0;
        bool acyclic = true;
        for (uint32_t i = 0; i < clique_count; i++) parent[i] = i;
        for (uint32_t i = 0; i < candidate_count; i++) {
            if ((mask & (UINT64_C(1) << i)) == 0) continue;
            uint32_t left = candidates[i].left;
            uint32_t right = candidates[i].right;
            if (ref_uf_find(parent, left) == ref_uf_find(parent, right)) {
                acyclic = false;
                break;
            }
            ref_uf_union(parent, left, right);
            weight += candidates[i].weight;
        }
        if (!acyclic) continue;
        uint32_t root = ref_uf_find(parent, 0);
        for (uint32_t i = 1; i < clique_count; i++) {
            if (ref_uf_find(parent, i) != root) acyclic = false;
        }
        if (!acyclic) continue;
        if (!found || weight > best_weight ||
            (weight == best_weight &&
             ref_tree_mask_preferred(mask, best_mask, candidate_count))) {
            found = true;
            best_weight = weight;
            best_mask = mask;
        }
    }
    if (!found) return false;

    uint64_t actual_mask = 0;
    for (guint i = 0; i < actual->tree_edges->len; i++) {
        const OspreyExactTreeEdge *edge = &g_array_index(
            actual->tree_edges, OspreyExactTreeEdge, i);
        bool matched = false;
        for (uint32_t j = 0; j < candidate_count; j++) {
            if (candidates[j].left == edge->left &&
                candidates[j].right == edge->right) {
                if ((actual_mask & (UINT64_C(1) << j)) != 0) return false;
                actual_mask |= UINT64_C(1) << j;
                matched = true;
                break;
            }
        }
        if (!matched) return false;
    }
    return actual_mask == best_mask;
}

static bool ref_component_validate(const OspreyExactBase *base,
                                   uint32_t component_id,
                                   const OspreyExactTopologyComponent *actual)
{
    const OspreyExactComponent *source;
    uint32_t count;
    bool adjacency[REF_MAX_VARS][REF_MAX_VARS] = {{ false }};
    bool live[REF_MAX_VARS] = { false };
    RefClique elimination[REF_MAX_VARS];
    RefClique maximal[REF_MAX_VARS];
    uint32_t maximal_count = 0;

    if (component_id >= base->components->len || actual == NULL ||
        actual->elimination_order == NULL ||
        actual->elimination_cliques == NULL || actual->cliques == NULL ||
        actual->tree_edges == NULL) {
        return false;
    }
    source = g_ptr_array_index(base->components, component_id);
    if (source == NULL || source->local_vars == NULL ||
        source->factor_refs == NULL || source->local_vars->len == 0 ||
        source->local_vars->len > REF_MAX_VARS) {
        return false;
    }
    count = source->local_vars->len;
    if (actual->elimination_order->len != count ||
        actual->elimination_cliques->len != count) {
        return false;
    }

    for (guint i = 0; i < source->factor_refs->len; i++) {
        uint32_t ref_id = g_array_index(source->factor_refs, uint32_t, i);
        if (ref_id >= base->factor_refs->len) return false;
        const OspreyExactFactorRef *factor = &g_array_index(
            base->factor_refs, OspreyExactFactorRef, ref_id);
        uint32_t positions[OSPREY_FACTOR_MAX_ARITY];
        for (uint32_t j = 0; j < factor->num_vars; j++) {
            if (!ref_local_position(source, factor->local_vars[j],
                                    &positions[j])) {
                return false;
            }
        }
        for (uint32_t j = 0; j < factor->num_vars; j++) {
            for (uint32_t k = j + 1; k < factor->num_vars; k++) {
                adjacency[positions[j]][positions[k]] = true;
                adjacency[positions[k]][positions[j]] = true;
            }
        }
    }
    for (uint32_t i = 0; i < count; i++) live[i] = true;

    for (uint32_t step = 0; step < count; step++) {
        uint64_t best_fill = UINT64_MAX;
        uint32_t best = UINT32_MAX;
        for (uint32_t candidate = 0; candidate < count; candidate++) {
            if (!live[candidate]) continue;
            uint64_t fill = 0;
            for (uint32_t i = 0; i < count; i++) {
                if (!live[i] || !adjacency[candidate][i]) continue;
                for (uint32_t j = i + 1; j < count; j++) {
                    if (live[j] && adjacency[candidate][j] &&
                        !adjacency[i][j]) {
                        fill++;
                    }
                }
            }
            uint32_t local = g_array_index(source->local_vars, uint32_t,
                                           candidate);
            uint32_t best_local = best == UINT32_MAX ? UINT32_MAX :
                g_array_index(source->local_vars, uint32_t, best);
            if (best == UINT32_MAX || fill < best_fill ||
                (fill == best_fill && local < best_local)) {
                best = candidate;
                best_fill = fill;
            }
        }
        if (best == UINT32_MAX) return false;
        uint32_t local = g_array_index(source->local_vars, uint32_t, best);
        if (g_array_index(actual->elimination_order, uint32_t, step) != local) {
            return false;
        }
        RefClique *clique = &elimination[step];
        memset(clique, 0, sizeof(*clique));
        for (uint32_t i = 0; i < count; i++) {
            if (live[i] && (i == best || adjacency[best][i])) {
                clique->vars[clique->count++] = g_array_index(
                    source->local_vars, uint32_t, i);
            }
        }
        qsort(clique->vars, clique->count, sizeof(clique->vars[0]),
              ref_u32_compare);
        if (!ref_actual_clique_equal(
                clique, g_ptr_array_index(actual->elimination_cliques,
                                           step))) {
            return false;
        }
        for (uint32_t i = 0; i < count; i++) {
            if (!live[i] || !adjacency[best][i]) continue;
            for (uint32_t j = i + 1; j < count; j++) {
                if (live[j] && adjacency[best][j]) {
                    adjacency[i][j] = true;
                    adjacency[j][i] = true;
                }
            }
        }
        live[best] = false;
    }

    for (uint32_t i = 0; i < count; i++) {
        bool duplicate = false;
        bool subset = false;
        for (uint32_t j = 0; j < i; j++) {
            if (ref_clique_equal(&elimination[i], &elimination[j])) {
                duplicate = true;
                break;
            }
        }
        if (duplicate) continue;
        for (uint32_t j = 0; j < count; j++) {
            if (ref_clique_strict_subset(&elimination[i], &elimination[j])) {
                subset = true;
                break;
            }
        }
        if (!subset) maximal[maximal_count++] = elimination[i];
    }
    qsort(maximal, maximal_count, sizeof(maximal[0]), ref_clique_compare);
    if (actual->cliques->len != maximal_count) return false;
    for (uint32_t i = 0; i < maximal_count; i++) {
        if (!ref_actual_clique_equal(
                &maximal[i], g_ptr_array_index(actual->cliques, i))) {
            return false;
        }
    }
    return ref_best_tree(maximal, maximal_count, actual);
}

bool stage4_exact_reference_validate(const OspreyExactBase *base,
                                     const OspreyExactTopology *topology)
{
    if (base == NULL || topology == NULL || base->components == NULL ||
        topology->components == NULL ||
        base->components->len != topology->components->len) {
        return false;
    }
    for (guint i = 0; i < base->components->len; i++) {
        if (!ref_component_validate(
                base, i, g_ptr_array_index(topology->components, i))) {
            return false;
        }
    }
    return true;
}

/* ------------------------------------------------------------------ */
/* Independent numerical oracle                                       */
/* ------------------------------------------------------------------ */

static bool ref_log_value_valid(double value)
{
    return isfinite(value) || value == -INFINITY;
}

static bool ref_logaddexp(double left, double right, double *out)
{
    double high;
    double low;
    double value;

    if (out == NULL || !ref_log_value_valid(left) ||
        !ref_log_value_valid(right)) return false;
    if (left == -INFINITY) {
        *out = right;
        return true;
    }
    if (right == -INFINITY) {
        *out = left;
        return true;
    }
    high = left > right ? left : right;
    low = left > right ? right : left;
    value = high + log1p(exp(low - high));
    if (!isfinite(value)) return false;
    *out = value;
    return true;
}

static bool ref_log_product(double left, double right, double *out)
{
    double value;

    if (out == NULL || !ref_log_value_valid(left) ||
        !ref_log_value_valid(right)) return false;
    if (left == -INFINITY || right == -INFINITY) {
        *out = -INFINITY;
        return true;
    }
    value = left + right;
    if (!isfinite(value)) return false;
    *out = value;
    return true;
}

static bool ref_factor_valid(const Stage4ReferenceFactor *spec,
                             uint32_t variable_count)
{
    if (spec == NULL || spec->stage != OSPREY_GRAPH_BASE_CA ||
        !isfinite(spec->probability) || spec->probability < 0.0 ||
        spec->probability > 1.0 || spec->num_vars == 0 ||
        spec->num_vars > 2 || spec->num_vars > OSPREY_FACTOR_MAX_ARITY ||
        spec->negative > 1) return false;
    if (spec->num_vars == 1) {
        if (spec->potential_kind != OSPREY_POTENTIAL_PRIOR ||
            spec->head_idx != 0) return false;
    } else if (spec->potential_kind != OSPREY_POTENTIAL_IMPLICATION ||
               spec->head_idx != 1) {
        return false;
    }
    for (uint32_t i = 0; i < spec->num_vars; i++) {
        if (spec->vars[i] >= variable_count) return false;
        for (uint32_t j = 0; j < i; j++) {
            if (spec->vars[j] == spec->vars[i]) return false;
        }
    }
    return true;
}

OspreyStatus stage4_exact_reference_bruteforce(
    const Stage4ReferenceProblem *problem, Stage4ReferenceSolution *solution)
{
    double numerator[STAGE4_REFERENCE_MAX_VARS];
    uint32_t canonical_order[STAGE4_REFERENCE_MAX_VARS];
    uint32_t canonical_by_variable[STAGE4_REFERENCE_MAX_VARS];
    uint64_t assignments;
    double logz = -INFINITY;

    if (problem == NULL || solution == NULL || problem->variables == NULL ||
        problem->factors == NULL || problem->variable_count == 0 ||
        problem->variable_count > STAGE4_REFERENCE_MAX_VARS ||
        problem->factor_count == 0) return OSPREY_INVALID_GRAPH;
    for (uint32_t i = 0; i < problem->variable_count; i++) {
        if (problem->variables[i].kind <= OSPREY_PRED_NONE ||
            problem->variables[i].kind >= OSPREY_PRED_COUNT) {
            return OSPREY_INVALID_GRAPH;
        }
        canonical_order[i] = i;
        numerator[i] = -INFINITY;
    }
    for (uint32_t i = 1; i < problem->variable_count; i++) {
        uint32_t value = canonical_order[i];
        uint32_t j = i;
        while (j != 0) {
            uint32_t previous = canonical_order[j - 1];
            const Stage4ReferenceVariable *left =
                &problem->variables[previous];
            const Stage4ReferenceVariable *right = &problem->variables[value];
            int comparison = left->kind < right->kind ? -1 :
                             left->kind != right->kind ? 1 :
                             osprey_var_payload_compare(
                                 left->kind, &left->payload, &right->payload);
            if (comparison <= 0) break;
            canonical_order[j] = previous;
            j--;
        }
        canonical_order[j] = value;
    }
    for (uint32_t i = 0; i < problem->variable_count; i++) {
        uint32_t variable = canonical_order[i];
        if (i != 0) {
            uint32_t previous = canonical_order[i - 1];
            const Stage4ReferenceVariable *left =
                &problem->variables[previous];
            const Stage4ReferenceVariable *right =
                &problem->variables[variable];
            if (left->kind == right->kind &&
                osprey_var_payload_compare(left->kind, &left->payload,
                                           &right->payload) == 0) {
                return OSPREY_INVALID_GRAPH;
            }
        }
        canonical_by_variable[variable] = i;
    }
    for (uint32_t i = 0; i < problem->factor_count; i++) {
        if (!ref_factor_valid(&problem->factors[i],
                              problem->variable_count)) {
            return OSPREY_INVALID_GRAPH;
        }
    }
    if (problem->variable_count >= sizeof(uint64_t) * 8u) {
        return OSPREY_INVALID_GRAPH;
    }
    assignments = UINT64_C(1) << problem->variable_count;
    for (uint64_t assignment = 0; assignment < assignments; assignment++) {
        double log_weight = 0.0;
        for (uint32_t i = 0; i < problem->factor_count; i++) {
            const Stage4ReferenceFactor *spec = &problem->factors[i];
            OspreyFactor factor;
            uint8_t values[OSPREY_FACTOR_MAX_ARITY] = { 0 };
            double term;

            memset(&factor, 0, sizeof(factor));
            factor.rule = spec->rule;
            factor.stage = spec->stage;
            factor.potential_kind = spec->potential_kind;
            factor.head_idx = spec->head_idx;
            factor.negative = spec->negative;
            factor.p = spec->probability;
            factor.num_vars = spec->num_vars;
            for (uint32_t j = 0; j < spec->num_vars; j++) {
                values[j] = (uint8_t)(
                    (assignment >> canonical_by_variable[spec->vars[j]]) & 1u);
            }
            if (!osprey_factor_log_weight(&factor, values, &term) ||
                !ref_log_product(log_weight, term, &log_weight)) {
                return OSPREY_INVALID_GRAPH;
            }
        }
        if (!ref_logaddexp(logz, log_weight, &logz)) {
            return OSPREY_INVALID_MODEL;
        }
        for (uint32_t i = 0; i < problem->variable_count; i++) {
            if (((assignment >> canonical_by_variable[i]) & 1u) != 0 &&
                !ref_logaddexp(numerator[i], log_weight, &numerator[i])) {
                return OSPREY_INVALID_MODEL;
            }
        }
    }
    if (!isfinite(logz)) return OSPREY_INVALID_MODEL;
    solution->logz = logz;
    for (uint32_t i = 0; i < problem->variable_count; i++) {
        double marginal;
        if (numerator[i] == -INFINITY) {
            marginal = 0.0;
        } else {
            double exponent = numerator[i] - logz;
            marginal = exp(exponent);
        }
        if (!isfinite(marginal) || marginal < 0.0 || marginal > 1.0) {
            return OSPREY_INVALID_MODEL;
        }
        solution->marginals[i] = marginal;
    }
    for (uint32_t i = problem->variable_count;
         i < STAGE4_REFERENCE_MAX_VARS; i++) {
        solution->marginals[i] = NAN;
    }
    return OSPREY_OK;
}
