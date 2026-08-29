/*
 * OSPREY exact-base projection and legacy inference.
 *
 * Stages 4.1-4.2 accept the immutable CA-only projection, canonical local
 * maps, retained factor validation, deterministic bounded clique topology,
 * exact factor ownership, and running-intersection validation. Stage 4.3
 * adds the atomic exact numerical pass; loopy BP and CC07 scheduling below
 * that boundary remain non-conformant and must not provide trusted marginals.
 * See agent-docs/info/OSPREY_TYPE_INFERENCE/STAGE4.md.
 *
 * Generic factor potentials are owned by osprey-graph.c.
 */

#include "osprey.h"
#include "osprey-internal.h"

#include <limits.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>

/* Diagnostic sink (snapshot.c). */
void log_msg(const char *fmt, ...);

#define OSPREY_BP_MAX_ITERS 500u
#define OSPREY_BP_TOL 1e-6
#define OSPREY_BP_CONVERGED_ROUNDS 10u
#define OSPREY_BP_DAMPING 0.5
#define OSPREY_BP_MAX_FOLD_ROUNDS 8u
#define OSPREY_P_UP 0.8
#define OSPREY_P_DN 0.2

/* ------------------------------------------------------------------ */
/* Region helpers                                                      */
/* ------------------------------------------------------------------ */

static bool region_eq(const OspreyRegionId *a, const OspreyRegionId *b) {
    return a->kind == b->kind && a->code_image_id == b->code_image_id &&
           a->site_offset == b->site_offset;
}

/* ------------------------------------------------------------------ */
/* Factor potential (§7.1)                                             */
/* ------------------------------------------------------------------ */

static double factor_value(const OspreyFactor *f, const uint32_t *bits) {
    uint8_t assignment[OSPREY_FACTOR_MAX_ARITY];
    double log_weight;
    if (f == NULL || f->num_vars > OSPREY_FACTOR_MAX_ARITY) return 0.0;
    for (uint32_t i = 0; i < f->num_vars; i++) {
        assignment[i] = bits[i] != 0;
    }
    if (!osprey_factor_log_weight(f, assignment, &log_weight)) return 0.0;
    return isinf(log_weight) && log_weight < 0.0 ? 0.0 : exp(log_weight);
}

/* ------------------------------------------------------------------ */
/* Stage 4.1: immutable CA-only projection and components              */
/* ------------------------------------------------------------------ */

static int exact_cmp_u64(uint64_t a, uint64_t b)
{
    return a < b ? -1 : a != b;
}

static int exact_cmp_i64(int64_t a, int64_t b)
{
    return a < b ? -1 : a != b;
}

static int exact_key_compare(const OspreyKey *a, const OspreyKey *b)
{
    int c = exact_cmp_u64(a->tag, b->tag);
    if (c != 0) return c;
    for (size_t i = 0; i < G_N_ELEMENTS(a->w); i++) {
        c = exact_cmp_u64(a->w[i], b->w[i]);
        if (c != 0) return c;
    }
    return 0;
}

static int exact_region_compare(const OspreyRegionId *a,
                                const OspreyRegionId *b)
{
    int c = exact_cmp_u64((uint64_t)a->kind, (uint64_t)b->kind);
    if (c != 0) return c;
    c = exact_cmp_u64(a->code_image_id, b->code_image_id);
    if (c != 0) return c;
    return exact_cmp_u64(a->site_offset, b->site_offset);
}

static int exact_address_compare(const OspreyAddress *a,
                                 const OspreyAddress *b)
{
    int c = exact_region_compare(&a->region, &b->region);
    return c != 0 ? c : exact_cmp_i64(a->offset, b->offset);
}

static bool exact_region_valid(const OspreyRegionId *region)
{
    return region != NULL && region->kind >= OSPREY_REGION_GLOBAL &&
           region->kind <= OSPREY_REGION_STACK_FUNCTION;
}

static bool exact_address_valid(const OspreyAddress *address)
{
    return address != NULL && exact_region_valid(&address->region);
}

static bool exact_chunk_valid(const OspreyChunk *chunk)
{
    return chunk != NULL && exact_address_valid(&chunk->address) &&
           chunk->size != 0;
}

static bool exact_payload_valid(uint8_t kind, const OspreyVarPayload *payload)
{
    int64_t span;

    if (payload == NULL) return false;
    switch (kind) {
    case OSPREY_PRED_PRIMITIVE_VAR:
    case OSPREY_PRED_SCALAR:
        return exact_chunk_valid(&payload->chunk);
    case OSPREY_PRED_PRIMITIVE_ACCESS:
        return exact_chunk_valid(&payload->prim_access.chunk);
    case OSPREY_PRED_UNFOLDABLE_HEAP:
    case OSPREY_PRED_FOLDABLE_HEAP:
        return exact_region_valid(&payload->heap_fold.region) &&
               payload->heap_fold.region.kind == OSPREY_REGION_HEAP_SITE;
    case OSPREY_PRED_HOMO_SEGMENT:
        return exact_address_valid(&payload->segment.a1) &&
               exact_address_valid(&payload->segment.a2) &&
               payload->segment.size > 0 &&
               exact_address_compare(&payload->segment.a1,
                                     &payload->segment.a2) <= 0;
    case OSPREY_PRED_ARRAY:
        if (!exact_address_valid(&payload->segment.a1) ||
            !exact_address_valid(&payload->segment.a2) ||
            exact_region_compare(&payload->segment.a1.region,
                                 &payload->segment.a2.region) != 0 ||
            payload->segment.a1.offset >= payload->segment.a2.offset ||
            payload->segment.size <= 0) {
            return false;
        }
        return osprey_check_sub(payload->segment.a2.offset,
                                payload->segment.a1.offset, &span) &&
               span >= payload->segment.size;
    case OSPREY_PRED_ARRAY_START:
        return exact_address_valid(&payload->addr);
    case OSPREY_PRED_FIELD_OF:
    case OSPREY_PRED_POINTER:
        return exact_chunk_valid(&payload->attached.chunk) &&
               exact_address_valid(&payload->attached.base);
    default:
        return false;
    }
}

static bool exact_rule_is_base(uint16_t rule)
{
    return rule >= OSPREY_RULE_CA01 && rule <= OSPREY_RULE_CA08;
}

static bool exact_base_implication_valid(const OspreyFactor *factor,
                                         const OspreyGraph *graph,
                                         bool negative, uint8_t source_kind,
                                         uint8_t target_kind,
                                         bool allow_reverse)
{
    if (factor->potential_kind != OSPREY_POTENTIAL_IMPLICATION ||
        factor->num_vars != 2 || factor->head_idx != 1 ||
        factor->negative != (negative ? 1 : 0)) {
        return false;
    }
    bool forward = true;
    bool reverse = allow_reverse;
    for (uint32_t i = 0; i + 1 < factor->num_vars; i++) {
        uint8_t kind = g_array_index(graph->vars, OspreyVar,
                                     factor->var_ids[i]).kind;
        if (kind != source_kind) forward = false;
        if (kind != target_kind) reverse = false;
    }
    uint8_t last_kind = g_array_index(graph->vars, OspreyVar,
                                      factor->var_ids[factor->num_vars - 1]).kind;
    return (forward && last_kind == target_kind) ||
           (reverse && last_kind == source_kind);
}

static bool exact_base_factor_valid(const OspreyFactor *factor,
                                    const OspreyGraph *graph)
{
    switch (factor->rule) {
    case OSPREY_RULE_CA01:
        return factor->potential_kind == OSPREY_POTENTIAL_PRIOR &&
               factor->num_vars == 1 && factor->head_idx == 0 &&
               !factor->negative &&
               g_array_index(graph->vars, OspreyVar,
                             factor->var_ids[0]).kind ==
                   OSPREY_PRED_PRIMITIVE_VAR;
    case OSPREY_RULE_CA02:
        return exact_base_implication_valid(
            factor, graph, false, OSPREY_PRED_PRIMITIVE_VAR,
            OSPREY_PRED_PRIMITIVE_VAR, false);
    case OSPREY_RULE_CA03:
        return exact_base_implication_valid(
            factor, graph, true, OSPREY_PRED_PRIMITIVE_VAR,
            OSPREY_PRED_PRIMITIVE_VAR, false);
    case OSPREY_RULE_CA04:
        return exact_base_implication_valid(
            factor, graph, false, OSPREY_PRED_PRIMITIVE_VAR,
            OSPREY_PRED_PRIMITIVE_ACCESS, false);
    case OSPREY_RULE_CA05:
        return exact_base_implication_valid(
            factor, graph, false, OSPREY_PRED_PRIMITIVE_ACCESS,
            OSPREY_PRED_PRIMITIVE_VAR, false);
    case OSPREY_RULE_CA06:
        return exact_base_implication_valid(
            factor, graph, false, OSPREY_PRED_PRIMITIVE_ACCESS,
            OSPREY_PRED_SCALAR, false);
    case OSPREY_RULE_CA07:
        return exact_base_implication_valid(
            factor, graph, false, OSPREY_PRED_SCALAR,
            OSPREY_PRED_SCALAR, false);
    case OSPREY_RULE_CA08:
        return exact_base_implication_valid(
            factor, graph, true, OSPREY_PRED_SCALAR,
            OSPREY_PRED_FIELD_OF, true);
    default:
        return false;
    }
}

static bool exact_factor_valid(const OspreyFactor *factor,
                               const OspreyGraph *graph)
{
    uint32_t variable_count = graph->vars->len;

    if (factor == NULL || factor->id == UINT32_MAX ||
        factor->rule <= OSPREY_RULE_NONE ||
        factor->rule >= OSPREY_RULE_COUNT ||
        (factor->stage != OSPREY_GRAPH_BASE_CA &&
         factor->stage != OSPREY_GRAPH_SECONDARY) ||
        (factor->stage == OSPREY_GRAPH_BASE_CA) !=
            exact_rule_is_base(factor->rule) ||
        (factor->potential_kind != OSPREY_POTENTIAL_IMPLICATION &&
         factor->potential_kind != OSPREY_POTENTIAL_PRIOR &&
         factor->potential_kind != OSPREY_POTENTIAL_HARD_FALSE) ||
        factor->negative > 1 || !isfinite(factor->p) || factor->p < 0.0 ||
        factor->p > 1.0 || factor->num_vars == 0 ||
        factor->num_vars > OSPREY_FACTOR_MAX_ARITY ||
        factor->var_ids == NULL) {
        return false;
    }

    switch (factor->potential_kind) {
    case OSPREY_POTENTIAL_PRIOR:
        if (factor->num_vars != 1 || factor->head_idx != 0) return false;
        break;
    case OSPREY_POTENTIAL_IMPLICATION:
        if (factor->num_vars < 2 || factor->head_idx >= factor->num_vars) {
            return false;
        }
        break;
    case OSPREY_POTENTIAL_HARD_FALSE:
        if (factor->rule != OSPREY_RULE_CB06 ||
            factor->stage != OSPREY_GRAPH_SECONDARY ||
            factor->num_vars != 1 || factor->head_idx != UINT16_MAX ||
            factor->negative || factor->p != 0.0) {
            return false;
        }
        break;
    default:
        return false;
    }

    for (uint32_t i = 0; i < factor->num_vars; i++) {
        if (factor->var_ids[i] >= variable_count) return false;
        for (uint32_t j = 0; j < i; j++) {
            if (factor->var_ids[j] == factor->var_ids[i]) return false;
        }
    }
    return factor->stage != OSPREY_GRAPH_BASE_CA ||
           exact_base_factor_valid(factor, graph);
}

typedef struct OspreyExactVarRef {
    OspreyKey key;
    OspreyVarPayload payload;
    uint32_t graph_var_id;
    uint8_t kind;
} OspreyExactVarRef;

static gint exact_var_ref_compare(gconstpointer ap, gconstpointer bp)
{
    const OspreyExactVarRef *a = ap;
    const OspreyExactVarRef *b = bp;
    int c = exact_cmp_u64(a->kind, b->kind);
    if (c == 0) {
        c = osprey_var_payload_compare(a->kind, &a->payload, &b->payload);
    }
    if (c == 0) c = exact_key_compare(&a->key, &b->key);
    return c != 0 ? c : exact_cmp_u64(a->graph_var_id, b->graph_var_id);
}

static gint exact_u32_compare(gconstpointer ap, gconstpointer bp)
{
    const uint32_t *a = ap;
    const uint32_t *b = bp;
    return exact_cmp_u64(*a, *b);
}

static uint32_t exact_uf_find(uint32_t *parent, uint32_t value)
{
    while (parent[value] != value) {
        parent[value] = parent[parent[value]];
        value = parent[value];
    }
    return value;
}

static void exact_uf_union(uint32_t *parent, uint32_t a, uint32_t b)
{
    uint32_t ra = exact_uf_find(parent, a);
    uint32_t rb = exact_uf_find(parent, b);
    if (ra == rb) return;
    if (ra < rb) parent[rb] = ra;
    else parent[ra] = rb;
}

static void exact_component_free(gpointer data)
{
    OspreyExactComponent *component = data;
    if (component == NULL) return;
    if (component->local_vars != NULL) {
        g_array_free(component->local_vars, TRUE);
    }
    if (component->factor_refs != NULL) {
        g_array_free(component->factor_refs, TRUE);
    }
    g_free(component);
}

void osprey_exact_base_free(OspreyExactBase *base)
{
    if (base == NULL) return;
    if (base->components != NULL) {
        g_ptr_array_free(base->components, TRUE);
    }
    if (base->factor_refs != NULL) {
        g_array_free(base->factor_refs, TRUE);
    }
    g_free(base->local_by_graph);
    if (base->graph_var_ids != NULL) {
        g_array_free(base->graph_var_ids, TRUE);
    }
    g_free(base);
}

static OspreyStatus exact_projection_failure(OspreyContext *ctx,
                                             OspreyStatus status)
{
    if (ctx != NULL && (ctx->last_status == OSPREY_OK ||
                        ctx->last_status == OSPREY_DISABLED)) {
        ctx->last_status = status;
    }
    return status;
}

typedef struct OspreyExactFactorSortContext {
    const OspreyGraph *graph;
} OspreyExactFactorSortContext;

static gint exact_factor_ref_identity_compare(
    const OspreyExactFactorRef *a, const OspreyExactFactorRef *b,
    const OspreyGraph *graph)
{
    const OspreyFactor *fa = g_array_index(graph->factors,
                                           OspreyFactor *,
                                           a->graph_factor_id);
    const OspreyFactor *fb = g_array_index(graph->factors,
                                           OspreyFactor *,
                                           b->graph_factor_id);
    int c = exact_cmp_u64(fa->stage, fb->stage);
    if (c != 0) return c;
    c = exact_cmp_u64(fa->rule, fb->rule);
    if (c != 0) return c;
    c = exact_cmp_u64(fa->potential_kind, fb->potential_kind);
    if (c != 0) return c;
    c = exact_cmp_u64(fa->negative, fb->negative);
    if (c != 0) return c;
    uint64_t ap_bits, bp_bits;
    memcpy(&ap_bits, &fa->p, sizeof(ap_bits));
    memcpy(&bp_bits, &fb->p, sizeof(bp_bits));
    c = exact_cmp_u64(ap_bits, bp_bits);
    if (c != 0) return c;
    c = exact_cmp_u64(fa->head_idx, fb->head_idx);
    if (c != 0) return c;
    c = exact_cmp_u64(a->num_vars, b->num_vars);
    if (c != 0) return c;
    for (uint32_t i = 0; i < a->num_vars; i++) {
        c = exact_cmp_u64(a->local_vars[i], b->local_vars[i]);
        if (c != 0) return c;
    }
    return 0;
}

static gint exact_factor_ref_compare(gconstpointer ap, gconstpointer bp,
                                     gpointer user_data)
{
    const OspreyExactFactorRef *a = ap;
    const OspreyExactFactorRef *b = bp;
    const OspreyExactFactorSortContext *context = user_data;
    int c = exact_factor_ref_identity_compare(a, b, context->graph);
    return c != 0 ? c : exact_cmp_u64(a->graph_factor_id,
                                       b->graph_factor_id);
}

static gint exact_component_compare(gconstpointer ap, gconstpointer bp)
{
    const OspreyExactComponent *a =
        *(OspreyExactComponent *const *)ap;
    const OspreyExactComponent *b =
        *(OspreyExactComponent *const *)bp;
    uint32_t a_first = g_array_index(a->local_vars, uint32_t, 0);
    uint32_t b_first = g_array_index(b->local_vars, uint32_t, 0);
    if (a_first != b_first) return exact_cmp_u64(a_first, b_first);
    uint32_t common = a->factor_refs->len < b->factor_refs->len
        ? a->factor_refs->len : b->factor_refs->len;
    for (uint32_t i = 0; i < common; i++) {
        uint32_t af = g_array_index(a->factor_refs, uint32_t, i);
        uint32_t bf = g_array_index(b->factor_refs, uint32_t, i);
        if (af != bf) return exact_cmp_u64(af, bf);
    }
    return exact_cmp_u64(a->factor_refs->len, b->factor_refs->len);
}

OspreyStatus osprey_exact_base_build(OspreyContext *ctx,
                                     OspreyExactBase **out)
{
    GArray *all_vars = NULL;
    GArray *base_factor_ids = NULL;
    uint8_t *base_marked = NULL;
    OspreyExactBase *base = NULL;
    uint32_t *parent = NULL;
    GHashTable *component_by_root = NULL;
    OspreyGraph *graph;
    uint32_t variable_count;
    OspreyStatus status = OSPREY_OK;

    if (out != NULL) *out = NULL;
    if (ctx == NULL || out == NULL || ctx->graph == NULL) {
        return exact_projection_failure(ctx, OSPREY_INVALID_GRAPH);
    }
    graph = ctx->graph;
    if (graph->vars == NULL || graph->factors == NULL) {
        return exact_projection_failure(ctx, OSPREY_INVALID_GRAPH);
    }
    variable_count = graph->vars->len;

    all_vars = g_array_sized_new(FALSE, FALSE, sizeof(OspreyExactVarRef),
                                 variable_count);
    for (uint32_t i = 0; i < variable_count; i++) {
        OspreyVar *variable = &g_array_index(graph->vars, OspreyVar, i);
        if (variable->id != i || variable->kind <= OSPREY_PRED_NONE ||
            variable->kind >= OSPREY_PRED_COUNT ||
            variable->hard_false > 1 || variable->region_limit_hit > 1 ||
            !isfinite(variable->prior) || variable->prior < 0.0 ||
            variable->prior > 1.0 ||
            !exact_payload_valid(variable->kind, &variable->payload)) {
            status = OSPREY_INVALID_GRAPH;
            goto fail;
        }
        OspreyExactVarRef ref;
        memset(&ref, 0, sizeof(ref));
        ref.key = osprey_var_key(variable->kind, &variable->payload);
        ref.payload = variable->payload;
        ref.graph_var_id = i;
        ref.kind = variable->kind;
        g_array_append_val(all_vars, ref);
    }
    g_array_sort(all_vars, exact_var_ref_compare);
    for (guint i = 1; i < all_vars->len; i++) {
        OspreyExactVarRef *previous = &g_array_index(all_vars,
                                                     OspreyExactVarRef,
                                                     i - 1);
        OspreyExactVarRef *current = &g_array_index(all_vars,
                                                     OspreyExactVarRef, i);
        if (exact_key_compare(&previous->key, &current->key) == 0) {
            status = OSPREY_INVALID_GRAPH;
            goto fail;
        }
    }

    base_factor_ids = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    base_marked = g_new0(uint8_t, variable_count);
    for (uint32_t i = 0; i < graph->factors->len; i++) {
        OspreyFactor *factor = g_array_index(graph->factors,
                                             OspreyFactor *, i);
        if (factor == NULL || factor->id != i ||
            !exact_factor_valid(factor, graph)) {
            status = OSPREY_INVALID_GRAPH;
            goto fail;
        }
        if (factor->stage != OSPREY_GRAPH_BASE_CA) continue;
        g_array_append_val(base_factor_ids, i);
        for (uint32_t j = 0; j < factor->num_vars; j++) {
            base_marked[factor->var_ids[j]] = 1;
        }
    }
    if (base_factor_ids->len == 0) {
        status = OSPREY_INCOMPLETE_FACTS;
        goto fail;
    }

    base = g_new0(OspreyExactBase, 1);
    base->graph_var_count = variable_count;
    base->graph_var_ids = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    base->local_by_graph = g_new(uint32_t, variable_count);
    for (uint32_t i = 0; i < variable_count; i++) {
        base->local_by_graph[i] = UINT32_MAX;
    }
    for (guint i = 0; i < all_vars->len; i++) {
        OspreyExactVarRef *ref = &g_array_index(all_vars,
                                                OspreyExactVarRef, i);
        if (!base_marked[ref->graph_var_id]) continue;
        uint32_t local_id = base->graph_var_ids->len;
        g_array_append_val(base->graph_var_ids, ref->graph_var_id);
        base->local_by_graph[ref->graph_var_id] = local_id;
    }
    if (base->graph_var_ids->len == 0) {
        status = OSPREY_INVALID_GRAPH;
        goto fail;
    }

    base->factor_refs = g_array_sized_new(FALSE, FALSE,
                                          sizeof(OspreyExactFactorRef),
                                          base_factor_ids->len);
    for (guint i = 0; i < base_factor_ids->len; i++) {
        uint32_t graph_factor_id = g_array_index(base_factor_ids, uint32_t, i);
        OspreyFactor *factor = g_array_index(graph->factors,
                                             OspreyFactor *,
                                             graph_factor_id);
        OspreyExactFactorRef ref;
        memset(&ref, 0, sizeof(ref));
        ref.graph_factor_id = graph_factor_id;
        ref.num_vars = factor->num_vars;
        for (uint32_t j = 0; j < factor->num_vars; j++) {
            uint32_t local_id = base->local_by_graph[factor->var_ids[j]];
            if (local_id == UINT32_MAX) {
                status = OSPREY_INVALID_GRAPH;
                goto fail;
            }
            ref.local_vars[j] = local_id;
        }
        g_array_append_val(base->factor_refs, ref);
    }
    OspreyExactFactorSortContext factor_context = { graph };
    g_array_sort_with_data(base->factor_refs, exact_factor_ref_compare,
                           &factor_context);
    for (guint i = 1; i < base->factor_refs->len; i++) {
        OspreyExactFactorRef *previous = &g_array_index(
            base->factor_refs, OspreyExactFactorRef, i - 1);
        OspreyExactFactorRef *current = &g_array_index(
            base->factor_refs, OspreyExactFactorRef, i);
        if (exact_factor_ref_identity_compare(previous, current, graph) == 0) {
            status = OSPREY_INVALID_GRAPH;
            goto fail;
        }
    }

    parent = g_new(uint32_t, base->graph_var_ids->len);
    for (uint32_t i = 0; i < base->graph_var_ids->len; i++) parent[i] = i;
    for (guint i = 0; i < base->factor_refs->len; i++) {
        OspreyExactFactorRef *ref = &g_array_index(base->factor_refs,
                                                   OspreyExactFactorRef, i);
        for (uint32_t j = 1; j < ref->num_vars; j++) {
            exact_uf_union(parent, ref->local_vars[0], ref->local_vars[j]);
        }
    }

    base->components = g_ptr_array_new_with_free_func(exact_component_free);
    component_by_root = g_hash_table_new(g_direct_hash, g_direct_equal);
    for (uint32_t i = 0; i < base->graph_var_ids->len; i++) {
        uint32_t root = exact_uf_find(parent, i);
        OspreyExactComponent *component = g_hash_table_lookup(
            component_by_root, GSIZE_TO_POINTER(root));
        if (component == NULL) {
            component = g_new0(OspreyExactComponent, 1);
            component->local_vars = g_array_new(FALSE, FALSE,
                                                sizeof(uint32_t));
            component->factor_refs = g_array_new(FALSE, FALSE,
                                                 sizeof(uint32_t));
            g_ptr_array_add(base->components, component);
            g_hash_table_insert(component_by_root, GSIZE_TO_POINTER(root),
                                component);
        }
        g_array_append_val(component->local_vars, i);
    }
    for (guint i = 0; i < base->factor_refs->len; i++) {
        OspreyExactFactorRef *ref = &g_array_index(base->factor_refs,
                                                   OspreyExactFactorRef, i);
        uint32_t root = exact_uf_find(parent, ref->local_vars[0]);
        OspreyExactComponent *component = g_hash_table_lookup(
            component_by_root, GSIZE_TO_POINTER(root));
        if (component == NULL) {
            status = OSPREY_INVALID_GRAPH;
            goto fail;
        }
        for (uint32_t j = 1; j < ref->num_vars; j++) {
            if (exact_uf_find(parent, ref->local_vars[j]) != root) {
                status = OSPREY_INVALID_GRAPH;
                goto fail;
            }
        }
        uint32_t factor_ref_id = i;
        g_array_append_val(component->factor_refs, factor_ref_id);
    }
    for (guint i = 0; i < base->components->len; i++) {
        OspreyExactComponent *component = g_ptr_array_index(
            base->components, i);
        g_array_sort(component->local_vars, exact_u32_compare);
        g_array_sort(component->factor_refs, exact_u32_compare);
        if (component->local_vars->len == 0 ||
            component->factor_refs->len == 0) {
            status = OSPREY_INVALID_GRAPH;
            goto fail;
        }
    }
    g_ptr_array_sort(base->components, exact_component_compare);

    g_hash_table_destroy(component_by_root);
    g_free(parent);
    g_free(base_marked);
    g_array_free(base_factor_ids, TRUE);
    g_array_free(all_vars, TRUE);
    *out = base;
    return OSPREY_OK;

fail:
    if (component_by_root != NULL) g_hash_table_destroy(component_by_root);
    g_free(parent);
    g_free(base_marked);
    if (base_factor_ids != NULL) g_array_free(base_factor_ids, TRUE);
    if (all_vars != NULL) g_array_free(all_vars, TRUE);
    osprey_exact_base_free(base);
    return exact_projection_failure(ctx, status);
}

/* ------------------------------------------------------------------ */
/* Stage 4.2: bounded clique topology                                 */
/* ------------------------------------------------------------------ */

#define OSPREY_DEFAULT_EXACT_TABLE_BYTES (256ULL * 1024ULL * 1024ULL)

/* A heap entry is generation-checked because min-fill scores are recomputed
 * only for variables whose live neighborhoods changed.  Canonical local IDs
 * are already in full predicate-key order in the Stage 4.1 projection. */
typedef struct ExactHeapEntry {
    uint64_t fill;
    uint32_t local;
    uint32_t generation;
} ExactHeapEntry;

typedef struct ExactCliquePair {
    uint32_t left;
    uint32_t right;
} ExactCliquePair;

typedef struct ExactTreeCandidate {
    uint32_t left;
    uint32_t right;
    uint32_t weight;
} ExactTreeCandidate;

static bool exact_u64_add(uint64_t a, uint64_t b, uint64_t *out)
{
    if (out == NULL || a > UINT64_MAX - b) return false;
    *out = a + b;
    return true;
}

static bool exact_size_mul(size_t a, size_t b, size_t *out)
{
    if (out == NULL || (b != 0 && a > SIZE_MAX / b)) return false;
    *out = a * b;
    return true;
}

static bool exact_size_add(size_t a, size_t b, size_t *out)
{
    if (out == NULL || a > SIZE_MAX - b) return false;
    *out = a + b;
    return true;
}

static bool exact_assignment_cells(uint32_t variables, uint64_t *out)
{
    uint64_t bits = (uint64_t)sizeof(size_t) * 8u;
    if (bits > sizeof(uint64_t) * 8u) bits = sizeof(uint64_t) * 8u;
    if (out == NULL || variables >= bits) return false;
    *out = (uint64_t)((size_t)1 << variables);
    return true;
}

static bool exact_topology_limits(const OspreyContext *ctx,
                                  uint64_t *clique_limit,
                                  uint64_t *workspace_limit)
{
    uint64_t width;
    uint64_t workspace;
    uint64_t bits = (uint64_t)sizeof(size_t) * 8u;
    if (bits > sizeof(uint64_t) * 8u) bits = sizeof(uint64_t) * 8u;

    if (ctx == NULL || clique_limit == NULL || workspace_limit == NULL) {
        return false;
    }
    width = ctx->config.max_exact_clique_vars;
    if (width == 0) width = 20;
    if (width >= bits) return false;
    workspace = ctx->config.max_exact_table_bytes;
    if (workspace == 0) workspace = OSPREY_DEFAULT_EXACT_TABLE_BYTES;
#if SIZE_MAX < UINT64_MAX
    if (workspace > SIZE_MAX) return false;
#endif
    *clique_limit = width;
    *workspace_limit = workspace;
    return true;
}

static OspreyExactClique *exact_clique_new(void)
{
    OspreyExactClique *clique = g_new0(OspreyExactClique, 1);
    clique->id = UINT32_MAX;
    clique->local_vars = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    clique->factor_refs = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    return clique;
}

static OspreyExactClique *exact_clique_clone(const OspreyExactClique *source)
{
    OspreyExactClique *copy;
    if (source == NULL || source->local_vars == NULL) return NULL;
    copy = exact_clique_new();
    g_array_append_vals(copy->local_vars, source->local_vars->data,
                        source->local_vars->len);
    return copy;
}

static void exact_clique_free(gpointer data)
{
    OspreyExactClique *clique = data;
    if (clique == NULL) return;
    if (clique->local_vars != NULL) g_array_free(clique->local_vars, TRUE);
    if (clique->factor_refs != NULL) g_array_free(clique->factor_refs, TRUE);
    g_free(clique);
}

static void exact_tree_edge_clear(OspreyExactTreeEdge *edge)
{
    if (edge != NULL && edge->separator != NULL) {
        g_array_free(edge->separator, TRUE);
        edge->separator = NULL;
    }
}

static void exact_topology_component_free(gpointer data)
{
    OspreyExactTopologyComponent *component = data;
    if (component == NULL) return;
    if (component->local_vars != NULL) {
        g_array_free(component->local_vars, TRUE);
    }
    if (component->elimination_order != NULL) {
        g_array_free(component->elimination_order, TRUE);
    }
    if (component->elimination_cliques != NULL) {
        g_ptr_array_free(component->elimination_cliques, TRUE);
    }
    if (component->cliques != NULL) {
        g_ptr_array_free(component->cliques, TRUE);
    }
    if (component->tree_edges != NULL) {
        for (guint i = 0; i < component->tree_edges->len; i++) {
            exact_tree_edge_clear(&g_array_index(component->tree_edges,
                                                  OspreyExactTreeEdge, i));
        }
        g_array_free(component->tree_edges, TRUE);
    }
    g_free(component);
}

void osprey_exact_topology_free(OspreyExactTopology *topology)
{
    if (topology == NULL) return;
    if (topology->components != NULL) {
        g_ptr_array_free(topology->components, TRUE);
    }
    if (topology->factor_owner != NULL) {
        g_array_free(topology->factor_owner, TRUE);
    }
    g_free(topology);
}

static int exact_clique_compare(const OspreyExactClique *a,
                                const OspreyExactClique *b)
{
    guint common;
    if (a == NULL || b == NULL) return a == b ? 0 : (a == NULL ? -1 : 1);
    common = a->local_vars->len < b->local_vars->len
        ? a->local_vars->len : b->local_vars->len;
    for (guint i = 0; i < common; i++) {
        uint32_t av = g_array_index(a->local_vars, uint32_t, i);
        uint32_t bv = g_array_index(b->local_vars, uint32_t, i);
        if (av != bv) return exact_cmp_u64(av, bv);
    }
    return exact_cmp_u64(a->local_vars->len, b->local_vars->len);
}

static gint exact_clique_ptr_compare(gconstpointer ap, gconstpointer bp)
{
    const OspreyExactClique *a = *(OspreyExactClique *const *)ap;
    const OspreyExactClique *b = *(OspreyExactClique *const *)bp;
    return exact_clique_compare(a, b);
}

static bool exact_clique_equal(const OspreyExactClique *a,
                               const OspreyExactClique *b)
{
    if (a == NULL || b == NULL || a->local_vars->len != b->local_vars->len) {
        return false;
    }
    for (guint i = 0; i < a->local_vars->len; i++) {
        if (g_array_index(a->local_vars, uint32_t, i) !=
            g_array_index(b->local_vars, uint32_t, i)) return false;
    }
    return true;
}

static bool exact_clique_contains(const OspreyExactClique *clique,
                                  uint32_t local)
{
    guint lo = 0;
    guint hi;
    if (clique == NULL || clique->local_vars == NULL) return false;
    hi = clique->local_vars->len;
    while (lo < hi) {
        guint mid = lo + (hi - lo) / 2;
        uint32_t value = g_array_index(clique->local_vars, uint32_t, mid);
        if (value == local) return true;
        if (value < local) lo = mid + 1;
        else hi = mid;
    }
    return false;
}

static bool exact_clique_contains_all(const OspreyExactClique *clique,
                                      const OspreyExactFactorRef *factor)
{
    if (clique == NULL || factor == NULL) return false;
    for (uint32_t i = 0; i < factor->num_vars; i++) {
        if (!exact_clique_contains(clique, factor->local_vars[i])) {
            return false;
        }
    }
    return true;
}

static OspreyExactClique *exact_smallest_owner(
    const OspreyExactTopologyComponent *component,
    const OspreyExactFactorRef *factor)
{
    OspreyExactClique *owner = NULL;
    if (component == NULL || factor == NULL || component->cliques == NULL) {
        return NULL;
    }
    for (guint i = 0; i < component->cliques->len; i++) {
        OspreyExactClique *candidate = g_ptr_array_index(component->cliques,
                                                           i);
        if (!exact_clique_contains_all(candidate, factor)) continue;
        if (owner == NULL || candidate->local_vars->len <
                                owner->local_vars->len ||
            (candidate->local_vars->len == owner->local_vars->len &&
             exact_clique_compare(candidate, owner) < 0)) {
            owner = candidate;
        }
    }
    return owner;
}

static bool exact_clique_subset(const OspreyExactClique *small,
                                const OspreyExactClique *large)
{
    guint i = 0;
    guint j = 0;
    if (small == NULL || large == NULL ||
        small->local_vars->len >= large->local_vars->len) return false;
    while (i < small->local_vars->len && j < large->local_vars->len) {
        uint32_t sv = g_array_index(small->local_vars, uint32_t, i);
        uint32_t lv = g_array_index(large->local_vars, uint32_t, j);
        if (sv == lv) {
            i++;
            j++;
        } else if (sv > lv) {
            j++;
        } else {
            return false;
        }
    }
    return i == small->local_vars->len;
}

static GPtrArray *exact_array_lists_new(uint32_t count)
{
    GPtrArray *lists = g_ptr_array_sized_new(count);
    for (uint32_t i = 0; i < count; i++) {
        g_ptr_array_add(lists, g_array_new(FALSE, FALSE, sizeof(uint32_t)));
    }
    return lists;
}

static void exact_array_lists_free(GPtrArray *lists)
{
    if (lists == NULL) return;
    for (guint i = 0; i < lists->len; i++) {
        GArray *array = g_ptr_array_index(lists, i);
        if (array != NULL) g_array_free(array, TRUE);
    }
    g_ptr_array_free(lists, TRUE);
}

static bool exact_local_position(const GArray *locals, uint32_t local,
                                 uint32_t *position)
{
    guint lo = 0;
    guint hi;
    if (locals == NULL || position == NULL) return false;
    hi = locals->len;
    while (lo < hi) {
        guint mid = lo + (hi - lo) / 2;
        uint32_t value = g_array_index(locals, uint32_t, mid);
        if (value == local) {
            *position = mid;
            return true;
        }
        if (value < local) lo = mid + 1;
        else hi = mid;
    }
    return false;
}

static bool exact_adj_insert(GArray *adj, uint32_t value, bool *inserted)
{
    guint lo = 0;
    guint hi;
    if (adj == NULL || inserted == NULL) return false;
    hi = adj->len;
    while (lo < hi) {
        guint mid = lo + (hi - lo) / 2;
        uint32_t current = g_array_index(adj, uint32_t, mid);
        if (current == value) {
            *inserted = false;
            return true;
        }
        if (current < value) lo = mid + 1;
        else hi = mid;
    }
    g_array_insert_val(adj, lo, value);
    *inserted = true;
    return true;
}

static bool exact_adj_remove(GArray *adj, uint32_t value)
{
    guint lo = 0;
    guint hi;
    if (adj == NULL) return false;
    hi = adj->len;
    while (lo < hi) {
        guint mid = lo + (hi - lo) / 2;
        uint32_t current = g_array_index(adj, uint32_t, mid);
        if (current == value) {
            g_array_remove_index(adj, mid);
            return true;
        }
        if (current < value) lo = mid + 1;
        else hi = mid;
    }
    return false;
}

static bool exact_adj_has(const GArray *adj, uint32_t value)
{
    guint lo = 0;
    guint hi;
    if (adj == NULL) return false;
    hi = adj->len;
    while (lo < hi) {
        guint mid = lo + (hi - lo) / 2;
        uint32_t current = g_array_index(adj, uint32_t, mid);
        if (current == value) return true;
        if (current < value) lo = mid + 1;
        else hi = mid;
    }
    return false;
}

static bool exact_adj_edge(GPtrArray *neighbors, uint32_t a, uint32_t b,
                           bool *inserted)
{
    bool first;
    bool second;
    if (neighbors == NULL || inserted == NULL || a == b ||
        a >= neighbors->len || b >= neighbors->len) return false;
    if (!exact_adj_insert(g_ptr_array_index(neighbors, a), b, &first) ||
        !exact_adj_insert(g_ptr_array_index(neighbors, b), a, &second)) {
        return false;
    }
    if (first != second) return false;
    *inserted = first;
    return true;
}

static bool exact_heap_before(const ExactHeapEntry *a,
                              const ExactHeapEntry *b)
{
    if (a->fill != b->fill) return a->fill < b->fill;
    return a->local < b->local;
}

static void exact_heap_swap(ExactHeapEntry *a, ExactHeapEntry *b)
{
    ExactHeapEntry temp = *a;
    *a = *b;
    *b = temp;
}

static void exact_heap_push(GArray *heap, ExactHeapEntry entry)
{
    guint index;
    if (heap == NULL) return;
    g_array_append_val(heap, entry);
    index = heap->len - 1;
    while (index != 0) {
        guint parent = (index - 1) / 2;
        ExactHeapEntry *current = &g_array_index(heap, ExactHeapEntry,
                                                  index);
        ExactHeapEntry *ancestor = &g_array_index(heap, ExactHeapEntry,
                                                   parent);
        if (!exact_heap_before(current, ancestor)) break;
        exact_heap_swap(current, ancestor);
        index = parent;
    }
}

static bool exact_heap_pop(GArray *heap, ExactHeapEntry *out)
{
    ExactHeapEntry replacement;
    guint index;
    if (heap == NULL || out == NULL || heap->len == 0) return false;
    *out = g_array_index(heap, ExactHeapEntry, 0);
    if (heap->len == 1) {
        g_array_set_size(heap, 0);
        return true;
    }
    replacement = g_array_index(heap, ExactHeapEntry, heap->len - 1);
    g_array_set_size(heap, heap->len - 1);
    g_array_index(heap, ExactHeapEntry, 0) = replacement;
    index = 0;
    for (;;) {
        guint left = index * 2 + 1;
        guint right = left + 1;
        guint best = index;
        if (left < heap->len && exact_heap_before(
                &g_array_index(heap, ExactHeapEntry, left),
                &g_array_index(heap, ExactHeapEntry, best))) best = left;
        if (right < heap->len && exact_heap_before(
                &g_array_index(heap, ExactHeapEntry, right),
                &g_array_index(heap, ExactHeapEntry, best))) best = right;
        if (best == index) break;
        exact_heap_swap(&g_array_index(heap, ExactHeapEntry, index),
                        &g_array_index(heap, ExactHeapEntry, best));
        index = best;
    }
    return true;
}

static bool exact_fill_score(GPtrArray *neighbors, const uint8_t *live,
                             uint32_t local, uint64_t *score)
{
    GArray *adj;
    uint64_t missing = 0;
    if (neighbors == NULL || live == NULL || score == NULL ||
        local >= neighbors->len || !live[local]) return false;
    adj = g_ptr_array_index(neighbors, local);
    for (guint i = 0; i < adj->len; i++) {
        uint32_t a = g_array_index(adj, uint32_t, i);
        if (!live[a]) continue;
        for (guint j = i + 1; j < adj->len; j++) {
            uint32_t b = g_array_index(adj, uint32_t, j);
            if (!live[b] || exact_adj_has(g_ptr_array_index(neighbors, a), b)) {
                continue;
            }
            if (missing == UINT64_MAX) return false;
            missing++;
        }
    }
    *score = missing;
    return true;
}

static void exact_mark_neighbors(GPtrArray *neighbors, const uint8_t *live,
                                 uint32_t local, uint8_t *affected)
{
    GArray *adj = g_ptr_array_index(neighbors, local);
    for (guint i = 0; i < adj->len; i++) {
        uint32_t value = g_array_index(adj, uint32_t, i);
        if (live[value]) affected[value] = 1;
    }
}

static guint exact_pair_hash(gconstpointer data)
{
    const ExactCliquePair *pair = data;
    uint64_t value = ((uint64_t)pair->left << 32) | pair->right;
    value ^= value >> 33;
    value *= 0xff51afd7ed558ccdULL;
    value ^= value >> 33;
    return (guint)value;
}

static gboolean exact_pair_equal(gconstpointer ap, gconstpointer bp)
{
    const ExactCliquePair *a = ap;
    const ExactCliquePair *b = bp;
    return a->left == b->left && a->right == b->right;
}

static gint exact_tree_candidate_compare(gconstpointer ap, gconstpointer bp)
{
    const ExactTreeCandidate *a = ap;
    const ExactTreeCandidate *b = bp;
    if (a->weight != b->weight) return a->weight > b->weight ? -1 : 1;
    if (a->left != b->left) return exact_cmp_u64(a->left, b->left);
    return exact_cmp_u64(a->right, b->right);
}

static bool exact_clique_intersection(const OspreyExactClique *a,
                                      const OspreyExactClique *b,
                                      GArray *out)
{
    guint i = 0;
    guint j = 0;
    if (a == NULL || b == NULL || out == NULL) return false;
    while (i < a->local_vars->len && j < b->local_vars->len) {
        uint32_t av = g_array_index(a->local_vars, uint32_t, i);
        uint32_t bv = g_array_index(b->local_vars, uint32_t, j);
        if (av == bv) {
            g_array_append_val(out, av);
            i++;
            j++;
        } else if (av < bv) {
            i++;
        } else {
            j++;
        }
    }
    return true;
}

/* Validate the accepted 4.1 projection again at the topology boundary. */
static bool exact_topology_base_valid(const OspreyContext *ctx,
                                      const OspreyExactBase *base)
{
    const OspreyGraph *graph;
    uint32_t graph_var_count;
    uint32_t local_var_count;
    uint32_t factor_count;
    uint32_t expected_factor_count = 0;
    uint8_t *expected_base_vars = NULL;
    uint8_t *seen_vars = NULL;
    uint32_t *component_of_var = NULL;
    uint8_t *seen_factors = NULL;
    uint8_t *seen_graph_factors = NULL;
    uint32_t *factor_component = NULL;
    bool valid = false;

    if (ctx == NULL || base == NULL || ctx->graph == NULL ||
        base->graph_var_ids == NULL || base->local_by_graph == NULL ||
        base->factor_refs == NULL || base->components == NULL) return false;
    graph = ctx->graph;
    if (graph->vars == NULL || graph->factors == NULL ||
        graph->vars->len != base->graph_var_count ||
        graph->vars->len > UINT32_MAX || graph->factors->len > UINT32_MAX ||
        base->graph_var_ids->len == 0 ||
        base->graph_var_ids->len > base->graph_var_count ||
        base->graph_var_count == 0 || base->factor_refs->len == 0 ||
        base->components->len == 0) return false;
    graph_var_count = base->graph_var_count;
    local_var_count = base->graph_var_ids->len;
    factor_count = base->factor_refs->len;
    expected_base_vars = g_new0(uint8_t, graph_var_count);
    seen_vars = g_new0(uint8_t, local_var_count);
    component_of_var = g_new(uint32_t, local_var_count);
    for (uint32_t i = 0; i < local_var_count; i++) {
        component_of_var[i] = UINT32_MAX;
    }
    seen_factors = g_new0(uint8_t, factor_count);
    seen_graph_factors = g_new0(uint8_t, graph->factors->len);
    factor_component = g_new(uint32_t, factor_count);
    for (uint32_t graph_id = 0; graph_id < graph->vars->len; graph_id++) {
        OspreyVar *var = &g_array_index(graph->vars, OspreyVar, graph_id);
        if (var->id != graph_id || var->kind <= OSPREY_PRED_NONE ||
            var->kind >= OSPREY_PRED_COUNT ||
            !exact_payload_valid(var->kind, &var->payload)) goto out;
    }
    for (uint32_t graph_factor_id = 0;
         graph_factor_id < graph->factors->len; graph_factor_id++) {
        OspreyFactor *factor = g_array_index(graph->factors,
                                             OspreyFactor *, graph_factor_id);
        if (factor == NULL || factor->id != graph_factor_id ||
            !exact_factor_valid(factor, graph)) goto out;
        if (factor->stage == OSPREY_GRAPH_BASE_CA) {
            if (expected_factor_count == UINT32_MAX) goto out;
            expected_factor_count++;
            for (uint32_t i = 0; i < factor->num_vars; i++) {
                expected_base_vars[factor->var_ids[i]] = 1;
            }
        }
    }
    if (expected_factor_count != factor_count) goto out;
    for (uint32_t i = 0; i < factor_count; i++) factor_component[i] = UINT32_MAX;

    for (uint32_t local = 0; local < local_var_count; local++) {
        uint32_t graph_id = g_array_index(base->graph_var_ids, uint32_t,
                                          local);
        OspreyVar *var;
        if (graph_id >= graph->vars->len ||
            base->local_by_graph[graph_id] != local || seen_vars[local]) {
            goto out;
        }
        var = &g_array_index(graph->vars, OspreyVar, graph_id);
        if (var->id != graph_id || var->kind <= OSPREY_PRED_NONE ||
            var->kind >= OSPREY_PRED_COUNT ||
            !exact_payload_valid(var->kind, &var->payload)) goto out;
        if (local != 0) {
            uint32_t previous_graph = g_array_index(base->graph_var_ids,
                                                    uint32_t, local - 1);
            OspreyVar *previous = &g_array_index(graph->vars, OspreyVar,
                                                  previous_graph);
            int order = exact_cmp_u64(previous->kind, var->kind);
            if (order == 0) {
                order = osprey_var_payload_compare(previous->kind,
                                                   &previous->payload,
                                                   &var->payload);
            }
            if (order >= 0) goto out;
        }
    }
    for (uint32_t graph_id = 0; graph_id < graph_var_count; graph_id++) {
        uint32_t local = base->local_by_graph[graph_id];
        if ((local != UINT32_MAX) != (expected_base_vars[graph_id] != 0)) {
            goto out;
        }
        if (local != UINT32_MAX &&
            (local >= local_var_count ||
             g_array_index(base->graph_var_ids, uint32_t, local) != graph_id)) {
            goto out;
        }
    }

    for (guint component_id = 0; component_id < base->components->len;
         component_id++) {
        OspreyExactComponent *component = g_ptr_array_index(
            base->components, component_id);
        if (component == NULL || component->local_vars == NULL ||
            component->factor_refs == NULL ||
            component->local_vars->len == 0 || component->factor_refs->len == 0) {
            goto out;
        }
        for (guint j = 0; j < component->local_vars->len; j++) {
            uint32_t local = g_array_index(component->local_vars, uint32_t, j);
            if (local >= local_var_count ||
                component_of_var[local] != UINT32_MAX ||
                (j != 0 && g_array_index(component->local_vars, uint32_t,
                                         j - 1) >= local)) goto out;
            component_of_var[local] = component_id;
            seen_vars[local] = 1;
        }
        for (guint j = 0; j < component->factor_refs->len; j++) {
            uint32_t ref_id = g_array_index(component->factor_refs,
                                             uint32_t, j);
            if (ref_id >= factor_count || seen_factors[ref_id] ||
                (j != 0 && g_array_index(component->factor_refs, uint32_t,
                                         j - 1) >= ref_id)) goto out;
            seen_factors[ref_id] = 1;
            factor_component[ref_id] = component_id;
        }
    }
    for (uint32_t local = 0; local < local_var_count; local++) {
        if (!seen_vars[local]) goto out;
    }
    for (uint32_t ref_id = 0; ref_id < factor_count; ref_id++) {
        OspreyExactFactorRef *ref = &g_array_index(base->factor_refs,
                                                    OspreyExactFactorRef,
                                                    ref_id);
        OspreyFactor *factor;
        if (!seen_factors[ref_id] || ref->num_vars == 0 ||
            ref->num_vars > OSPREY_FACTOR_MAX_ARITY ||
            ref->graph_factor_id >= graph->factors->len ||
            seen_graph_factors[ref->graph_factor_id]) goto out;
        factor = g_array_index(graph->factors, OspreyFactor *,
                               ref->graph_factor_id);
        if (factor == NULL || factor->stage != OSPREY_GRAPH_BASE_CA ||
            !exact_factor_valid(factor, graph) ||
            factor->num_vars != ref->num_vars) goto out;
        seen_graph_factors[ref->graph_factor_id] = 1;
        for (uint32_t j = 0; j < ref->num_vars; j++) {
            uint32_t local = ref->local_vars[j];
            if (local >= local_var_count ||
                component_of_var[local] != factor_component[ref_id]) {
                goto out;
            }
            for (uint32_t k = 0; k < j; k++) {
                if (ref->local_vars[k] == local) goto out;
            }
            if (g_array_index(base->graph_var_ids, uint32_t, local) !=
                factor->var_ids[j]) goto out;
        }
    }
    for (uint32_t graph_factor_id = 0;
         graph_factor_id < graph->factors->len; graph_factor_id++) {
        OspreyFactor *factor = g_array_index(graph->factors,
                                             OspreyFactor *, graph_factor_id);
        if (factor->stage == OSPREY_GRAPH_BASE_CA &&
            !seen_graph_factors[graph_factor_id]) {
            goto out;
        }
    }
    valid = true;
out:
    g_free(expected_base_vars);
    g_free(seen_vars);
    g_free(component_of_var);
    g_free(seen_factors);
    g_free(seen_graph_factors);
    g_free(factor_component);
    return valid;
}

static OspreyStatus exact_component_workspace(
    OspreyExactTopologyComponent *component, uint64_t workspace_limit,
    uint64_t *required, const char **limit_kind)
{
    size_t total_bytes = 0;
    uint64_t assignment_cells = 0;
    uint64_t separator_cells = 0;

    if (required != NULL) *required = 0;
    if (limit_kind != NULL) *limit_kind = NULL;
    if (component == NULL || component->cliques == NULL ||
        component->tree_edges == NULL) return OSPREY_INVALID_GRAPH;

    for (guint i = 0; i < component->cliques->len; i++) {
        OspreyExactClique *clique = g_ptr_array_index(component->cliques, i);
        uint64_t cells;
        size_t bytes;
        if (clique == NULL || clique->local_vars == NULL ||
            !exact_assignment_cells(clique->local_vars->len, &cells) ||
            !exact_u64_add(assignment_cells, cells, &assignment_cells) ||
            cells > SIZE_MAX ||
            !exact_size_mul((size_t)cells, sizeof(double), &bytes) ||
            !exact_size_add(total_bytes, bytes, &total_bytes)) {
            if (required != NULL) *required = UINT64_MAX;
            if (limit_kind != NULL) *limit_kind = "workspace";
            return OSPREY_EXACT_COMPONENT_TOO_LARGE;
        }
        clique->assignment_cells = cells;
    }
    for (guint i = 0; i < component->tree_edges->len; i++) {
        OspreyExactTreeEdge *edge = &g_array_index(
            component->tree_edges, OspreyExactTreeEdge, i);
        uint64_t cells;
        size_t directed_cells;
        size_t bytes;
        if (edge->separator == NULL ||
            !exact_assignment_cells(edge->separator->len, &cells) ||
            !exact_size_mul((size_t)cells, 2, &directed_cells) ||
            !exact_u64_add(separator_cells, (uint64_t)directed_cells,
                           &separator_cells) ||
            !exact_size_mul(directed_cells, sizeof(double), &bytes) ||
            !exact_size_add(total_bytes, bytes, &total_bytes)) {
            if (required != NULL) *required = UINT64_MAX;
            if (limit_kind != NULL) *limit_kind = "workspace";
            return OSPREY_EXACT_COMPONENT_TOO_LARGE;
        }
        edge->separator_cells = cells;
    }
    component->assignment_cells = assignment_cells;
    component->separator_cells = separator_cells;
    component->table_bytes = (uint64_t)total_bytes;
    if ((uint64_t)total_bytes > workspace_limit) {
        if (required != NULL) *required = (uint64_t)total_bytes;
        if (limit_kind != NULL) *limit_kind = "workspace";
        return OSPREY_EXACT_COMPONENT_TOO_LARGE;
    }
    return OSPREY_OK;
}

static OspreyStatus exact_component_topology_build(
    const OspreyExactBase *base, uint32_t base_component_id,
    uint64_t clique_limit, uint64_t workspace_limit,
    OspreyExactTopologyComponent *component, uint64_t *required,
    const char **limit_kind)
{
    const OspreyExactComponent *source;
    uint32_t component_size;
    uint32_t base_variable_count;
    uint32_t *position_by_local = NULL;
    GPtrArray *neighbors = NULL;
    uint8_t *live = NULL;
    uint8_t *affected = NULL;
    uint32_t *connectivity = NULL;
    uint64_t *scores = NULL;
    uint32_t *generations = NULL;
    GArray *heap = NULL;
    GPtrArray *unique_refs = NULL;
    GPtrArray *incidence = NULL;
    GPtrArray *max_incidence = NULL;
    GHashTable *pairs = NULL;
    GArray *candidates = NULL;
    GArray *tree_uf = NULL;
    uint32_t *clique_parent = NULL;
    GArray *queue = NULL;
    OspreyStatus status = OSPREY_OK;
    uint32_t remaining;

    if (required != NULL) *required = 0;
    if (limit_kind != NULL) *limit_kind = NULL;
    if (base == NULL || component == NULL ||
        base_component_id >= base->components->len) return OSPREY_INVALID_GRAPH;
    source = g_ptr_array_index(base->components, base_component_id);
    if (source == NULL || source->local_vars == NULL ||
        source->factor_refs == NULL || source->local_vars->len == 0 ||
        source->local_vars->len > UINT32_MAX) return OSPREY_INVALID_GRAPH;
    component_size = source->local_vars->len;
    base_variable_count = base->graph_var_ids->len;

    component->base_component = base_component_id;
    component->local_vars = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    g_array_append_vals(component->local_vars, source->local_vars->data,
                        source->local_vars->len);
    component->elimination_order = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    component->elimination_cliques = g_ptr_array_new_with_free_func(
        exact_clique_free);
    component->cliques = g_ptr_array_new_with_free_func(exact_clique_free);
    component->tree_edges = g_array_new(FALSE, FALSE,
                                        sizeof(OspreyExactTreeEdge));
    component->root_clique = UINT32_MAX;

    position_by_local = g_new(uint32_t, base_variable_count);
    for (uint32_t i = 0; i < base_variable_count; i++) {
        position_by_local[i] = UINT32_MAX;
    }
    for (uint32_t i = 0; i < component_size; i++) {
        uint32_t local = g_array_index(source->local_vars, uint32_t, i);
        if (local >= base_variable_count || position_by_local[local] !=
                                            UINT32_MAX) {
            status = OSPREY_INVALID_GRAPH;
            goto cleanup;
        }
        position_by_local[local] = i;
    }

    neighbors = exact_array_lists_new(component_size);
    connectivity = g_new(uint32_t, component_size);
    for (uint32_t i = 0; i < component_size; i++) connectivity[i] = i;

    /* Re-derive primal connectivity and adjacency from the retained factor
     * scopes.  This intentionally does not use graph->uf_parent. */
    for (guint i = 0; i < source->factor_refs->len; i++) {
        uint32_t ref_id = g_array_index(source->factor_refs, uint32_t, i);
        const OspreyExactFactorRef *ref;
        uint32_t positions[OSPREY_FACTOR_MAX_ARITY];
        if (ref_id >= base->factor_refs->len) {
            status = OSPREY_INVALID_GRAPH;
            goto cleanup;
        }
        ref = &g_array_index(base->factor_refs, OspreyExactFactorRef,
                             ref_id);
        if (ref->num_vars == 0 || ref->num_vars > OSPREY_FACTOR_MAX_ARITY) {
            status = OSPREY_INVALID_GRAPH;
            goto cleanup;
        }
        for (uint32_t j = 0; j < ref->num_vars; j++) {
            uint32_t position;
            if (!exact_local_position(source->local_vars, ref->local_vars[j],
                                      &position)) {
                status = OSPREY_INVALID_GRAPH;
                goto cleanup;
            }
            positions[j] = position;
            for (uint32_t k = 0; k < j; k++) {
                if (positions[k] == position) {
                    status = OSPREY_INVALID_GRAPH;
                    goto cleanup;
                }
            }
            if (j != 0) exact_uf_union(connectivity, positions[0], position);
        }
        for (uint32_t j = 0; j < ref->num_vars; j++) {
            for (uint32_t k = j + 1; k < ref->num_vars; k++) {
                bool inserted;
                if (!exact_adj_edge(neighbors, positions[j], positions[k],
                                    &inserted)) {
                    status = OSPREY_INVALID_GRAPH;
                    goto cleanup;
                }
            }
        }
    }
    {
        uint32_t root = exact_uf_find(connectivity, 0);
        for (uint32_t i = 1; i < component_size; i++) {
            if (exact_uf_find(connectivity, i) != root) {
                status = OSPREY_INVALID_GRAPH;
                goto cleanup;
            }
        }
    }

    live = g_new0(uint8_t, component_size);
    affected = g_new0(uint8_t, component_size);
    scores = g_new0(uint64_t, component_size);
    generations = g_new0(uint32_t, component_size);
    heap = g_array_new(FALSE, FALSE, sizeof(ExactHeapEntry));
    for (uint32_t i = 0; i < component_size; i++) live[i] = 1;
    for (uint32_t i = 0; i < component_size; i++) {
        if (!exact_fill_score(neighbors, live, i, &scores[i])) {
            status = OSPREY_INVALID_GRAPH;
            goto cleanup;
        }
        ExactHeapEntry entry = { scores[i], i, generations[i] };
        exact_heap_push(heap, entry);
    }

    remaining = component_size;
    while (remaining != 0) {
        ExactHeapEntry entry;
        uint32_t variable;
        GArray *variable_neighbors;
        OspreyExactClique *clique;

        for (;;) {
            if (!exact_heap_pop(heap, &entry) || entry.local >= component_size) {
                status = OSPREY_INVALID_GRAPH;
                goto cleanup;
            }
            if (live[entry.local] && entry.generation ==
                                         generations[entry.local] &&
                entry.fill == scores[entry.local]) break;
        }
        variable = entry.local;
        variable_neighbors = g_ptr_array_index(neighbors, variable);
        clique = exact_clique_new();
        {
            uint32_t local = g_array_index(source->local_vars, uint32_t,
                                           variable);
            g_array_append_val(clique->local_vars, local);
            g_array_append_val(component->elimination_order, local);
        }
        for (guint i = 0; i < variable_neighbors->len; i++) {
            uint32_t position = g_array_index(variable_neighbors, uint32_t, i);
            if (live[position]) {
                uint32_t local = g_array_index(source->local_vars, uint32_t,
                                               position);
                g_array_append_val(clique->local_vars, local);
            }
        }
        g_array_sort(clique->local_vars, exact_u32_compare);
        if (clique->local_vars->len > clique_limit) {
            g_ptr_array_add(component->elimination_cliques, clique);
            if (required != NULL) *required = clique->local_vars->len;
            if (limit_kind != NULL) *limit_kind = "clique";
            status = OSPREY_EXACT_COMPONENT_TOO_LARGE;
            goto cleanup;
        }
        g_ptr_array_add(component->elimination_cliques, clique);

        memset(affected, 0, component_size);
        for (guint i = 0; i < variable_neighbors->len; i++) {
            uint32_t position = g_array_index(variable_neighbors, uint32_t, i);
            if (live[position]) affected[position] = 1;
        }
        for (guint i = 0; i < variable_neighbors->len; i++) {
            uint32_t left = g_array_index(variable_neighbors, uint32_t, i);
            if (!live[left]) continue;
            for (guint j = i + 1; j < variable_neighbors->len; j++) {
                uint32_t right = g_array_index(variable_neighbors, uint32_t,
                                                j);
                bool inserted;
                if (!live[right]) continue;
                if (!exact_adj_edge(neighbors, left, right, &inserted)) {
                    status = OSPREY_INVALID_GRAPH;
                    goto cleanup;
                }
                if (inserted) {
                    affected[left] = 1;
                    affected[right] = 1;
                    exact_mark_neighbors(neighbors, live, left, affected);
                    exact_mark_neighbors(neighbors, live, right, affected);
                }
            }
        }
        live[variable] = 0;
        for (guint i = 0; i < variable_neighbors->len; i++) {
            uint32_t position = g_array_index(variable_neighbors, uint32_t, i);
            if (live[position] &&
                !exact_adj_remove(g_ptr_array_index(neighbors, position),
                                  variable)) {
                status = OSPREY_INVALID_GRAPH;
                goto cleanup;
            }
        }
        g_array_set_size(variable_neighbors, 0);
        remaining--;

        for (uint32_t i = 0; i < component_size; i++) {
            if (!affected[i] || !live[i]) continue;
            if (!exact_fill_score(neighbors, live, i, &scores[i]) ||
                generations[i] == UINT32_MAX) {
                status = OSPREY_INVALID_GRAPH;
                goto cleanup;
            }
            generations[i]++;
            ExactHeapEntry updated = { scores[i], i, generations[i] };
            exact_heap_push(heap, updated);
        }
    }

    /* Deduplicate elimination cliques, then remove strict subsets.  The
     * incidence lists avoid an unconditional clique-count squared scan: a
     * possible superset must share at least one member with the candidate. */
    unique_refs = g_ptr_array_new();
    for (guint i = 0; i < component->elimination_cliques->len; i++) {
        g_ptr_array_add(unique_refs,
                        g_ptr_array_index(component->elimination_cliques, i));
    }
    g_ptr_array_sort(unique_refs, exact_clique_ptr_compare);
    {
        GPtrArray *unique = g_ptr_array_new();
        for (guint i = 0; i < unique_refs->len; i++) {
            OspreyExactClique *clique = g_ptr_array_index(unique_refs, i);
            if (unique->len == 0 || !exact_clique_equal(
                    clique, g_ptr_array_index(unique, unique->len - 1))) {
                g_ptr_array_add(unique, clique);
            }
        }
        g_ptr_array_free(unique_refs, TRUE);
        unique_refs = unique;
    }
    incidence = exact_array_lists_new(component_size);
    for (guint i = 0; i < unique_refs->len; i++) {
        OspreyExactClique *clique = g_ptr_array_index(unique_refs, i);
        for (guint j = 0; j < clique->local_vars->len; j++) {
            uint32_t local = g_array_index(clique->local_vars, uint32_t, j);
            uint32_t position = position_by_local[local];
            if (position == UINT32_MAX) {
                status = OSPREY_INVALID_GRAPH;
                goto cleanup;
            }
            g_array_append_val(g_ptr_array_index(incidence, position), i);
        }
    }
    for (guint i = 0; i < unique_refs->len; i++) {
        OspreyExactClique *clique = g_ptr_array_index(unique_refs, i);
        uint32_t rare_position = UINT32_MAX;
        guint rare_count = G_MAXUINT;
        bool dominated = false;
        for (guint j = 0; j < clique->local_vars->len; j++) {
            uint32_t local = g_array_index(clique->local_vars, uint32_t, j);
            uint32_t position = position_by_local[local];
            GArray *members = g_ptr_array_index(incidence, position);
            if (members->len < rare_count) {
                rare_count = members->len;
                rare_position = position;
            }
        }
        if (rare_position == UINT32_MAX) {
            status = OSPREY_INVALID_GRAPH;
            goto cleanup;
        }
        GArray *members = g_ptr_array_index(incidence, rare_position);
        for (guint j = 0; j < members->len; j++) {
            guint candidate_index = g_array_index(members, uint32_t, j);
            OspreyExactClique *candidate = g_ptr_array_index(unique_refs,
                                                              candidate_index);
            if (candidate_index != i && exact_clique_subset(clique, candidate)) {
                dominated = true;
                break;
            }
        }
        if (!dominated) {
            OspreyExactClique *copy = exact_clique_clone(clique);
            if (copy == NULL) {
                status = OSPREY_INVALID_GRAPH;
                goto cleanup;
            }
            g_ptr_array_add(component->cliques, copy);
        }
    }
    g_ptr_array_sort(component->cliques, exact_clique_ptr_compare);
    if (component->cliques->len == 0) {
        status = OSPREY_INVALID_GRAPH;
        goto cleanup;
    }
    component->max_clique_vars = 0;
    for (guint i = 0; i < component->cliques->len; i++) {
        OspreyExactClique *clique = g_ptr_array_index(component->cliques, i);
        if (clique->local_vars->len > component->max_clique_vars) {
            component->max_clique_vars = clique->local_vars->len;
        }
    }
    for (uint32_t i = 0; i < component_size; i++) {
        uint32_t local = g_array_index(source->local_vars, uint32_t, i);
        bool present = false;
        for (guint j = 0; j < component->cliques->len; j++) {
            if (exact_clique_contains(g_ptr_array_index(component->cliques, j),
                                      local)) {
                present = true;
                break;
            }
        }
        if (!present) {
            status = OSPREY_INVALID_GRAPH;
            goto cleanup;
        }
    }

    /* Enumerate only clique pairs sharing a variable, using the incidence
     * index.  The map stores the checked intersection cardinality. */
    max_incidence = exact_array_lists_new(component_size);
    for (guint i = 0; i < component->cliques->len; i++) {
        OspreyExactClique *clique = g_ptr_array_index(component->cliques, i);
        for (guint j = 0; j < clique->local_vars->len; j++) {
            uint32_t local = g_array_index(clique->local_vars, uint32_t, j);
            uint32_t position = position_by_local[local];
            if (position == UINT32_MAX) {
                status = OSPREY_INVALID_GRAPH;
                goto cleanup;
            }
            g_array_append_val(g_ptr_array_index(max_incidence, position), i);
        }
    }
    pairs = g_hash_table_new_full(exact_pair_hash, exact_pair_equal,
                                  g_free, g_free);
    for (uint32_t position = 0; position < component_size; position++) {
        GArray *members = g_ptr_array_index(max_incidence, position);
        for (guint i = 0; i < members->len; i++) {
            for (guint j = i + 1; j < members->len; j++) {
                uint32_t a = g_array_index(members, uint32_t, i);
                uint32_t b = g_array_index(members, uint32_t, j);
                ExactCliquePair lookup = {
                    a < b ? a : b, a < b ? b : a
                };
                uint32_t *weight = g_hash_table_lookup(pairs, &lookup);
                if (weight == NULL) {
                    ExactCliquePair *key = g_new(ExactCliquePair, 1);
                    uint32_t *value = g_new(uint32_t, 1);
                    *key = lookup;
                    *value = 1;
                    g_hash_table_insert(pairs, key, value);
                } else if (*weight == UINT32_MAX) {
                    status = OSPREY_INVALID_GRAPH;
                    goto cleanup;
                } else {
                    (*weight)++;
                }
            }
        }
    }
    candidates = g_array_new(FALSE, FALSE, sizeof(ExactTreeCandidate));
    {
        GHashTableIter iter;
        gpointer key_data;
        gpointer value_data;
        g_hash_table_iter_init(&iter, pairs);
        while (g_hash_table_iter_next(&iter, &key_data, &value_data)) {
            ExactCliquePair *pair = key_data;
            uint32_t weight = *(uint32_t *)value_data;
            ExactTreeCandidate candidate = { pair->left, pair->right,
                                             weight };
            g_array_append_val(candidates, candidate);
        }
    }
    g_array_sort(candidates, exact_tree_candidate_compare);
    tree_uf = g_array_sized_new(FALSE, FALSE, sizeof(uint32_t),
                                component->cliques->len);
    for (guint i = 0; i < component->cliques->len; i++) {
        uint32_t value = i;
        g_array_append_val(tree_uf, value);
    }
    for (guint i = 0; i < candidates->len &&
                       component->tree_edges->len + 1 <
                           component->cliques->len; i++) {
        ExactTreeCandidate candidate = g_array_index(candidates,
                                                      ExactTreeCandidate, i);
        uint32_t left_root;
        uint32_t right_root;
        OspreyExactTreeEdge edge;
        if (candidate.left >= component->cliques->len ||
            candidate.right >= component->cliques->len ||
            candidate.left >= candidate.right) {
            status = OSPREY_INVALID_GRAPH;
            goto cleanup;
        }
        left_root = exact_uf_find((uint32_t *)tree_uf->data, candidate.left);
        right_root = exact_uf_find((uint32_t *)tree_uf->data, candidate.right);
        if (left_root == right_root) continue;
        memset(&edge, 0, sizeof(edge));
        edge.left = candidate.left;
        edge.right = candidate.right;
        edge.parent = UINT32_MAX;
        edge.child = UINT32_MAX;
        edge.separator = g_array_new(FALSE, FALSE, sizeof(uint32_t));
        if (!exact_clique_intersection(
                g_ptr_array_index(component->cliques, edge.left),
                g_ptr_array_index(component->cliques, edge.right),
                edge.separator) || edge.separator->len != candidate.weight) {
            exact_tree_edge_clear(&edge);
            status = OSPREY_INVALID_GRAPH;
            goto cleanup;
        }
        g_array_append_val(component->tree_edges, edge);
        exact_uf_union((uint32_t *)tree_uf->data, candidate.left,
                       candidate.right);
    }
    if (component->cliques->len == 0 ||
        component->tree_edges->len + 1 != component->cliques->len) {
        status = OSPREY_INVALID_GRAPH;
        goto cleanup;
    }

    /* Root the selected tree at the smallest canonical clique. */
    exact_array_lists_free(max_incidence);
    max_incidence = NULL;
    max_incidence = exact_array_lists_new(component->cliques->len);
    for (guint i = 0; i < component->tree_edges->len; i++) {
        OspreyExactTreeEdge *edge = &g_array_index(
            component->tree_edges, OspreyExactTreeEdge, i);
        g_array_append_val(g_ptr_array_index(max_incidence, edge->left), i);
        g_array_append_val(g_ptr_array_index(max_incidence, edge->right), i);
    }
    clique_parent = g_new(uint32_t, component->cliques->len);
    for (guint i = 0; i < component->cliques->len; i++) {
        clique_parent[i] = UINT32_MAX;
    }
    queue = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    component->root_clique = 0;
    clique_parent[0] = 0;
    {
        uint32_t root = 0;
        g_array_append_val(queue, root);
    }
    for (guint q = 0; q < queue->len; q++) {
        uint32_t current = g_array_index(queue, uint32_t, q);
        GArray *edge_ids = g_ptr_array_index(max_incidence, current);
        for (guint i = 0; i < edge_ids->len; i++) {
            uint32_t edge_id = g_array_index(edge_ids, uint32_t, i);
            OspreyExactTreeEdge *edge = &g_array_index(
                component->tree_edges, OspreyExactTreeEdge, edge_id);
            uint32_t other = edge->left == current ? edge->right : edge->left;
            if (clique_parent[other] == UINT32_MAX) {
                clique_parent[other] = current;
                g_array_append_val(queue, other);
            }
        }
    }
    if (queue->len != component->cliques->len) {
        status = OSPREY_INVALID_GRAPH;
        goto cleanup;
    }
    for (guint i = 0; i < component->tree_edges->len; i++) {
        OspreyExactTreeEdge *edge = &g_array_index(
            component->tree_edges, OspreyExactTreeEdge, i);
        if (clique_parent[edge->right] == edge->left) {
            edge->parent = edge->left;
            edge->child = edge->right;
        } else if (clique_parent[edge->left] == edge->right) {
            edge->parent = edge->right;
            edge->child = edge->left;
        } else {
            status = OSPREY_INVALID_GRAPH;
            goto cleanup;
        }
    }
    /* Edge storage is a canonical rooted representation, not a hash order. */
    for (guint i = 1; i < component->tree_edges->len; i++) {
        OspreyExactTreeEdge value = g_array_index(component->tree_edges,
                                                  OspreyExactTreeEdge, i);
        guint j = i;
        while (j != 0) {
            OspreyExactTreeEdge *previous = &g_array_index(
                component->tree_edges, OspreyExactTreeEdge, j - 1);
            if (previous->parent < value.parent ||
                (previous->parent == value.parent &&
                 previous->child <= value.child)) break;
            g_array_index(component->tree_edges, OspreyExactTreeEdge, j) =
                *previous;
            j--;
        }
        g_array_index(component->tree_edges, OspreyExactTreeEdge, j) = value;
    }

    status = exact_component_workspace(component, workspace_limit, required,
                                       limit_kind);

cleanup:
    if (queue != NULL) g_array_free(queue, TRUE);
    g_free(clique_parent);
    if (max_incidence != NULL) exact_array_lists_free(max_incidence);
    if (tree_uf != NULL) g_array_free(tree_uf, TRUE);
    if (candidates != NULL) g_array_free(candidates, TRUE);
    if (pairs != NULL) g_hash_table_destroy(pairs);
    if (incidence != NULL) exact_array_lists_free(incidence);
    if (unique_refs != NULL) g_ptr_array_free(unique_refs, TRUE);
    if (heap != NULL) g_array_free(heap, TRUE);
    g_free(generations);
    g_free(scores);
    g_free(affected);
    g_free(live);
    g_free(connectivity);
    if (neighbors != NULL) exact_array_lists_free(neighbors);
    g_free(position_by_local);
    return status;
}

static void exact_topology_limit_log(uint32_t component,
                                      const char *kind, uint64_t required,
                                      uint64_t limit)
{
    log_msg("[osprey] [infer] [exact] [large component %u] [%s %llu] "
            "[limit %llu]\n", component, kind != NULL ? kind : "workspace",
            (unsigned long long)required, (unsigned long long)limit);
}

OspreyStatus osprey_exact_topology_build(
    OspreyContext *ctx, const OspreyExactBase *base,
    OspreyExactTopology **out)
{
    OspreyExactTopology *topology = NULL;
    uint64_t clique_limit;
    uint64_t workspace_limit;
    uint64_t required = 0;
    const char *limit_kind = NULL;
    bool limit_logged = false;
    OspreyStatus status = OSPREY_OK;

    if (out != NULL) *out = NULL;
    if (ctx == NULL || out == NULL ||
        !exact_topology_limits(ctx, &clique_limit, &workspace_limit)) {
        if (ctx != NULL) {
            exact_topology_limit_log(UINT32_MAX, "configuration", 0, 0);
        }
        return exact_projection_failure(ctx,
                                        OSPREY_EXACT_COMPONENT_TOO_LARGE);
    }
    if (!exact_topology_base_valid(ctx, base)) {
        return exact_projection_failure(ctx, OSPREY_INVALID_GRAPH);
    }

    topology = g_new0(OspreyExactTopology, 1);
    topology->components = g_ptr_array_new_with_free_func(
        exact_topology_component_free);
    topology->factor_owner = g_array_sized_new(FALSE, FALSE, sizeof(uint32_t),
                                                base->factor_refs->len);
    for (guint i = 0; i < base->factor_refs->len; i++) {
        uint32_t invalid = UINT32_MAX;
        g_array_append_val(topology->factor_owner, invalid);
    }
    topology->variable_count = base->graph_var_ids->len;
    topology->factor_count = base->factor_refs->len;

    for (guint i = 0; i < base->components->len; i++) {
        OspreyExactTopologyComponent *component = g_new0(
            OspreyExactTopologyComponent, 1);
        status = exact_component_topology_build(
            base, i, clique_limit, workspace_limit, component, &required,
            &limit_kind);
        if (status != OSPREY_OK) {
            exact_topology_component_free(component);
            if (status == OSPREY_EXACT_COMPONENT_TOO_LARGE) {
                exact_topology_limit_log(i, limit_kind, required,
                                         limit_kind != NULL &&
                                         strcmp(limit_kind, "clique") == 0
                                             ? clique_limit : workspace_limit);
                limit_logged = true;
            }
            goto fail;
        }
        g_ptr_array_add(topology->components, component);
    }

    /* Assign stable flattened IDs only after every component has its
     * canonical maximal-clique order. */
    for (guint i = 0; i < topology->components->len; i++) {
        OspreyExactTopologyComponent *component = g_ptr_array_index(
            topology->components, i);
        for (guint j = 0; j < component->cliques->len; j++) {
            OspreyExactClique *clique = g_ptr_array_index(component->cliques,
                                                           j);
            if (topology->clique_count >= UINT32_MAX) {
                status = OSPREY_EXACT_COMPONENT_TOO_LARGE;
                required = topology->clique_count + 1;
                limit_kind = "workspace";
                goto fail;
            }
            clique->id = (uint32_t)topology->clique_count;
            topology->clique_count++;
        }
        if (component->max_clique_vars > topology->max_clique_vars) {
            topology->max_clique_vars = component->max_clique_vars;
        }
        if (!exact_u64_add(topology->table_bytes, component->table_bytes,
                           &topology->table_bytes)) {
            status = OSPREY_EXACT_COMPONENT_TOO_LARGE;
            required = UINT64_MAX;
            limit_kind = "workspace";
            goto fail;
        }
        if (component->table_bytes > topology->max_component_table_bytes) {
            topology->max_component_table_bytes = component->table_bytes;
        }
    }

    /* Assign each retained base factor to the smallest containing maximal
     * clique.  The base factor order is canonical and owner ties use the
     * canonical clique list order. */
    for (guint component_id = 0; component_id < base->components->len;
         component_id++) {
        const OspreyExactComponent *source = g_ptr_array_index(
            base->components, component_id);
        OspreyExactTopologyComponent *component = g_ptr_array_index(
            topology->components, component_id);
        for (guint j = 0; j < source->factor_refs->len; j++) {
            uint32_t ref_id = g_array_index(source->factor_refs, uint32_t, j);
            const OspreyExactFactorRef *ref = &g_array_index(
                base->factor_refs, OspreyExactFactorRef, ref_id);
            OspreyExactClique *owner = NULL;
            for (guint k = 0; k < component->cliques->len; k++) {
                OspreyExactClique *candidate = g_ptr_array_index(
                    component->cliques, k);
                if (!exact_clique_contains_all(candidate, ref)) continue;
                if (owner == NULL ||
                    candidate->local_vars->len < owner->local_vars->len ||
                    (candidate->local_vars->len == owner->local_vars->len &&
                     exact_clique_compare(candidate, owner) < 0)) {
                    owner = candidate;
                }
            }
            if (owner == NULL || ref_id >= topology->factor_owner->len ||
                g_array_index(topology->factor_owner, uint32_t, ref_id) !=
                    UINT32_MAX) {
                status = OSPREY_INVALID_GRAPH;
                goto fail;
            }
            g_array_append_val(owner->factor_refs, ref_id);
            g_array_index(topology->factor_owner, uint32_t, ref_id) =
                owner->id;
        }
    }
    if (!osprey_exact_topology_validate(ctx, base, topology)) {
        status = OSPREY_INVALID_GRAPH;
        goto fail;
    }

    *out = topology;
    return OSPREY_OK;

fail:
    if (status == OSPREY_EXACT_COMPONENT_TOO_LARGE && !limit_logged) {
        exact_topology_limit_log(UINT32_MAX, limit_kind, required,
                                 limit_kind != NULL &&
                                 strcmp(limit_kind, "clique") == 0
                                     ? clique_limit : workspace_limit);
    }
    osprey_exact_topology_free(topology);
    return exact_projection_failure(ctx, status);
}

static bool exact_component_workspace_valid(
    const OspreyExactTopologyComponent *component, uint64_t workspace_limit,
    uint64_t *table_bytes, uint64_t *assignment_cells,
    uint64_t *separator_cells)
{
    size_t total = 0;
    uint64_t assignments = 0;
    uint64_t separators = 0;
    if (component == NULL || component->cliques == NULL ||
        component->tree_edges == NULL || table_bytes == NULL ||
        assignment_cells == NULL || separator_cells == NULL) return false;
    for (guint i = 0; i < component->cliques->len; i++) {
        const OspreyExactClique *clique = g_ptr_array_index(
            component->cliques, i);
        uint64_t cells;
        size_t bytes;
        if (clique == NULL || clique->local_vars == NULL ||
            !exact_assignment_cells(clique->local_vars->len, &cells) ||
            clique->assignment_cells != cells ||
            !exact_u64_add(assignments, cells, &assignments) ||
            !exact_size_mul((size_t)cells, sizeof(double), &bytes) ||
            !exact_size_add(total, bytes, &total)) return false;
    }
    for (guint i = 0; i < component->tree_edges->len; i++) {
        const OspreyExactTreeEdge *edge = &g_array_index(
            component->tree_edges, OspreyExactTreeEdge, i);
        uint64_t cells;
        size_t directed_cells;
        size_t bytes;
        if (edge->separator == NULL || !exact_assignment_cells(
                edge->separator->len, &cells) ||
            edge->separator_cells != cells ||
            !exact_size_mul((size_t)cells, 2, &directed_cells) ||
            !exact_u64_add(separators, directed_cells, &separators) ||
            !exact_size_mul(directed_cells, sizeof(double), &bytes) ||
            !exact_size_add(total, bytes, &total)) return false;
    }
    if ((uint64_t)total > workspace_limit ||
        component->assignment_cells != assignments ||
        component->separator_cells != separators ||
        component->table_bytes != (uint64_t)total) return false;
    *table_bytes = (uint64_t)total;
    *assignment_cells = assignments;
    *separator_cells = separators;
    return true;
}

static bool exact_topology_membership_valid(
    const OspreyExactTopologyComponent *component,
    const OspreyExactClique *clique)
{
    if (component == NULL || clique == NULL || clique->local_vars == NULL ||
        clique->local_vars->len == 0) return false;
    for (guint i = 0; i < clique->local_vars->len; i++) {
        uint32_t local = g_array_index(clique->local_vars, uint32_t, i);
        uint32_t position;
        if (!exact_local_position(component->local_vars, local, &position)) {
            return false;
        }
        (void)position;
        if (i != 0 && g_array_index(clique->local_vars, uint32_t, i - 1) >=
                          local) return false;
    }
    return true;
}

static bool exact_topology_clique_contains_component_local(
    const OspreyExactTopologyComponent *component,
    const OspreyExactClique *clique, uint32_t local)
{
    uint32_t position;
    return component != NULL && clique != NULL &&
           exact_local_position(component->local_vars, local, &position) &&
           exact_clique_contains(clique, local);
}

bool osprey_exact_topology_validate(
    const OspreyContext *ctx, const OspreyExactBase *base,
    const OspreyExactTopology *topology)
{
    uint64_t clique_limit;
    uint64_t workspace_limit;
    uint32_t variable_count;
    uint32_t factor_count;
    uint8_t *seen_components = NULL;
    uint8_t *seen_variables = NULL;
    uint8_t *seen_factors = NULL;
    bool valid = false;
    uint64_t actual_cliques = 0;
    uint64_t actual_max_clique = 0;
    uint64_t actual_table_bytes = 0;
    uint64_t actual_max_component_bytes = 0;
    uint32_t expected_clique_id = 0;

    if (!exact_topology_limits(ctx, &clique_limit, &workspace_limit) ||
        !exact_topology_base_valid(ctx, base) || topology == NULL ||
        topology->components == NULL || topology->factor_owner == NULL) {
        return false;
    }
    variable_count = base->graph_var_ids->len;
    factor_count = base->factor_refs->len;
    if (topology->variable_count != variable_count ||
        topology->factor_count != factor_count ||
        topology->components->len != base->components->len ||
        topology->factor_owner->len != factor_count ||
        variable_count == 0 || factor_count == 0) return false;

    seen_components = g_new0(uint8_t, base->components->len);
    seen_variables = g_new0(uint8_t, variable_count);
    seen_factors = g_new0(uint8_t, factor_count);

    for (guint component_id = 0; component_id < topology->components->len;
         component_id++) {
        const OspreyExactTopologyComponent *component = g_ptr_array_index(
            topology->components, component_id);
        const OspreyExactComponent *source;
        uint32_t component_size;
        uint8_t *eliminated = NULL;
        uint32_t *tree_parent = NULL;
        uint32_t *root_parent = NULL;
        GHashTable *edge_pairs = NULL;
        uint64_t table_bytes;
        uint64_t assignment_cells;
        uint64_t separator_cells;

        if (component == NULL || component->base_component >=
                                      base->components->len ||
            seen_components[component->base_component] ||
            component->base_component != component_id ||
            component->local_vars == NULL ||
            component->local_vars->len == 0 ||
            component->elimination_order == NULL ||
            component->elimination_cliques == NULL ||
            component->cliques == NULL || component->tree_edges == NULL) {
            goto out;
        }
        seen_components[component->base_component] = 1;
        source = g_ptr_array_index(base->components,
                                   component->base_component);
        if (source == NULL || component->local_vars->len !=
                                  source->local_vars->len ||
            component->elimination_order->len !=
                component->local_vars->len ||
            component->elimination_cliques->len !=
                component->local_vars->len) goto component_out;
        component_size = component->local_vars->len;
        for (guint i = 0; i < component_size; i++) {
            uint32_t local = g_array_index(component->local_vars, uint32_t, i);
            if (local != g_array_index(source->local_vars, uint32_t, i) ||
                (i != 0 && g_array_index(component->local_vars, uint32_t,
                                          i - 1) >= local) ||
                local >= variable_count || seen_variables[local]) {
                goto component_out;
            }
            seen_variables[local] = 1;
        }
        eliminated = g_new0(uint8_t, component_size);
        for (guint i = 0; i < component->elimination_order->len; i++) {
            uint32_t local = g_array_index(component->elimination_order,
                                           uint32_t, i);
            uint32_t position;
            OspreyExactClique *clique = g_ptr_array_index(
                component->elimination_cliques, i);
            if (!exact_local_position(component->local_vars, local, &position) ||
                eliminated[position] || !exact_topology_membership_valid(
                    component, clique) || clique->local_vars->len >
                    clique_limit || !exact_clique_contains(clique, local)) {
                goto component_out;
            }
            eliminated[position] = 1;
        }
        for (uint32_t i = 0; i < component_size; i++) {
            if (!eliminated[i]) goto component_out;
        }

        for (guint i = 0; i < component->cliques->len; i++) {
            OspreyExactClique *clique = g_ptr_array_index(component->cliques, i);
            if (clique == NULL || clique->factor_refs == NULL ||
                clique->id != expected_clique_id ||
                !exact_topology_membership_valid(component, clique) ||
                clique->local_vars->len > clique_limit ||
                (i != 0 && exact_clique_compare(
                    g_ptr_array_index(component->cliques, i - 1), clique) >= 0)) {
                goto component_out;
            }
            bool was_elimination_clique = false;
            for (guint j = 0; j < component->elimination_cliques->len; j++) {
                if (exact_clique_equal(
                        clique, g_ptr_array_index(
                            component->elimination_cliques, j))) {
                    was_elimination_clique = true;
                    break;
                }
            }
            if (!was_elimination_clique) goto component_out;
            expected_clique_id++;
            for (guint j = 0; j < clique->local_vars->len; j++) {
                uint32_t local = g_array_index(clique->local_vars, uint32_t, j);
                if (!exact_topology_clique_contains_component_local(
                        component, clique, local)) goto component_out;
            }
        }
        if (component->cliques->len == 0 || component->root_clique != 0) {
            goto component_out;
        }
        for (guint i = 0; i < component->cliques->len; i++) {
            for (guint j = 0; j < component->cliques->len; j++) {
                if (i != j && exact_clique_subset(
                        g_ptr_array_index(component->cliques, i),
                        g_ptr_array_index(component->cliques, j))) {
                    goto component_out;
                }
            }
        }
        for (uint32_t i = 0; i < component_size; i++) {
            uint32_t local = g_array_index(component->local_vars, uint32_t, i);
            bool present = false;
            for (guint j = 0; j < component->cliques->len; j++) {
                if (exact_clique_contains(
                        g_ptr_array_index(component->cliques, j), local)) {
                    present = true;
                    break;
                }
            }
            if (!present) goto component_out;
        }

        edge_pairs = g_hash_table_new_full(exact_pair_hash,
                                           exact_pair_equal, g_free, NULL);
        tree_parent = g_new(uint32_t, component->cliques->len);
        root_parent = g_new(uint32_t, component->cliques->len);
        for (guint i = 0; i < component->cliques->len; i++) {
            tree_parent[i] = i;
            root_parent[i] = UINT32_MAX;
        }
        root_parent[0] = 0;
        if (component->tree_edges->len + 1 != component->cliques->len) {
            goto component_out;
        }
        for (guint i = 0; i < component->tree_edges->len; i++) {
            OspreyExactTreeEdge *edge = &g_array_index(
                component->tree_edges, OspreyExactTreeEdge, i);
            GArray *expected_separator;
            ExactCliquePair *pair;
            if (edge->left >= component->cliques->len ||
                edge->right >= component->cliques->len ||
                edge->left >= edge->right || edge->parent >=
                    component->cliques->len || edge->child >=
                    component->cliques->len || edge->parent == edge->child ||
                edge->separator == NULL || edge->separator->len == 0)
                goto component_out;
            pair = g_new(ExactCliquePair, 1);
            pair->left = edge->left;
            pair->right = edge->right;
            if (g_hash_table_contains(edge_pairs, pair)) {
                g_free(pair);
                goto component_out;
            }
            g_hash_table_insert(edge_pairs, pair, GINT_TO_POINTER(1));
            expected_separator = g_array_new(FALSE, FALSE, sizeof(uint32_t));
            if (!exact_clique_intersection(
                    g_ptr_array_index(component->cliques, edge->left),
                    g_ptr_array_index(component->cliques, edge->right),
                    expected_separator) ||
                expected_separator->len != edge->separator->len) {
                g_array_free(expected_separator, TRUE);
                goto component_out;
            }
            for (guint j = 0; j < expected_separator->len; j++) {
                if (g_array_index(expected_separator, uint32_t, j) !=
                    g_array_index(edge->separator, uint32_t, j)) {
                    g_array_free(expected_separator, TRUE);
                    goto component_out;
                }
            }
            g_array_free(expected_separator, TRUE);
            if (exact_uf_find(tree_parent, edge->left) ==
                exact_uf_find(tree_parent, edge->right)) goto component_out;
            exact_uf_union(tree_parent, edge->left, edge->right);
            if (root_parent[edge->child] != UINT32_MAX ||
                (edge->parent != edge->left && edge->parent != edge->right)) {
                goto component_out;
            }
            root_parent[edge->child] = edge->parent;
            if (!((edge->parent == edge->left && edge->child == edge->right) ||
                  (edge->parent == edge->right && edge->child == edge->left))) {
                goto component_out;
            }
        }
        {
            uint32_t root = exact_uf_find(tree_parent, 0);
            for (guint i = 1; i < component->cliques->len; i++) {
                if (exact_uf_find(tree_parent, i) != root ||
                    root_parent[i] == UINT32_MAX) goto component_out;
            }
        }
        /* In a rooted tree, the cliques containing one variable form a
         * connected subtree iff exactly one of them is the root of that
         * subtree: either the global root or a clique whose parent does not
         * contain the variable. */
        for (uint32_t local_position = 0; local_position < component_size;
             local_position++) {
            uint32_t local = g_array_index(component->local_vars, uint32_t,
                                           local_position);
            uint32_t entries = 0;
            for (guint i = 0; i < component->cliques->len; i++) {
                OspreyExactClique *clique = g_ptr_array_index(
                    component->cliques, i);
                if (!exact_clique_contains(clique, local)) continue;
                if (i == component->root_clique ||
                    !exact_clique_contains(g_ptr_array_index(
                        component->cliques, root_parent[i]), local)) {
                    entries++;
                }
            }
            if (entries != 1) {
                goto component_out;
            }
        }
        for (guint i = 0; i < component->cliques->len; i++) {
            OspreyExactClique *clique = g_ptr_array_index(component->cliques, i);
            for (guint j = 0; j < clique->factor_refs->len; j++) {
                uint32_t ref_id = g_array_index(clique->factor_refs,
                                                uint32_t, j);
                const OspreyExactFactorRef *ref;
                if (ref_id >= factor_count || seen_factors[ref_id] ||
                    (j != 0 && g_array_index(clique->factor_refs, uint32_t,
                                             j - 1) >= ref_id) ||
                    g_array_index(topology->factor_owner, uint32_t, ref_id) !=
                        clique->id) goto component_out;
                ref = &g_array_index(base->factor_refs,
                                      OspreyExactFactorRef, ref_id);
                if (!exact_clique_contains_all(clique, ref) ||
                    exact_smallest_owner(component, ref) != clique) {
                    goto component_out;
                }
                seen_factors[ref_id] = 1;
            }
        }
        if (!exact_component_workspace_valid(component, workspace_limit,
                                             &table_bytes, &assignment_cells,
                                             &separator_cells)) goto component_out;
        {
            uint32_t maximum = 0;
            for (guint i = 0; i < component->cliques->len; i++) {
                OspreyExactClique *clique = g_ptr_array_index(
                    component->cliques, i);
                if (clique->local_vars->len > maximum) maximum =
                    clique->local_vars->len;
            }
            if (component->max_clique_vars == 0 ||
                component->max_clique_vars > clique_limit ||
                component->max_clique_vars != maximum) goto component_out;
        }
        if (!exact_u64_add(actual_cliques, component->cliques->len,
                           &actual_cliques) ||
            !exact_u64_add(actual_table_bytes, table_bytes,
                           &actual_table_bytes)) goto component_out;
        if (component->max_clique_vars > actual_max_clique) {
            actual_max_clique = component->max_clique_vars;
        }
        if (table_bytes > actual_max_component_bytes) {
            actual_max_component_bytes = table_bytes;
        }
        g_hash_table_destroy(edge_pairs);
        edge_pairs = NULL;
        g_free(tree_parent);
        tree_parent = NULL;
        g_free(root_parent);
        root_parent = NULL;
        g_free(eliminated);
        eliminated = NULL;
        continue;

component_out:
        if (edge_pairs != NULL) g_hash_table_destroy(edge_pairs);
        g_free(tree_parent);
        g_free(root_parent);
        g_free(eliminated);
        goto out;
    }
    for (guint i = 0; i < base->components->len; i++) {
        if (!seen_components[i]) goto out;
    }
    for (uint32_t i = 0; i < variable_count; i++) {
        if (!seen_variables[i]) goto out;
    }
    for (uint32_t i = 0; i < factor_count; i++) {
        if (!seen_factors[i] || g_array_index(topology->factor_owner,
                                              uint32_t, i) == UINT32_MAX) {
            goto out;
        }
    }
    if (topology->clique_count != actual_cliques ||
        topology->max_clique_vars != actual_max_clique ||
        topology->table_bytes != actual_table_bytes ||
        topology->max_component_table_bytes != actual_max_component_bytes ||
        expected_clique_id != topology->clique_count) goto out;
    valid = true;
out:
    g_free(seen_components);
    g_free(seen_variables);
    g_free(seen_factors);
    return valid;
}

/* ------------------------------------------------------------------ */
/* Stage 4.3: exact log-domain junction-tree inference                 */

#define OSPREY_EXACT_MARGINAL_TOL 1e-10

typedef struct OspreyExactNumericMessage {
    double *parent_to_child;
    double *child_to_parent;
    uint64_t cells;
    double parent_to_child_log_norm;
    double child_to_parent_log_norm;
    bool parent_to_child_ready;
    bool child_to_parent_ready;
} OspreyExactNumericMessage;

typedef struct OspreyExactNumericEdgeMap {
    uint32_t count;
    uint32_t *parent_positions;
    uint32_t *child_positions;
} OspreyExactNumericEdgeMap;

typedef struct OspreyExactNumericWorkspace {
    uint32_t clique_count;
    uint32_t edge_count;
    double **clique_potentials;
    OspreyExactNumericMessage *messages;
    OspreyExactNumericEdgeMap *edge_maps;
    uint32_t *parent_edge;
    uint32_t *preorder;
} OspreyExactNumericWorkspace;

/* Test-only fault injection for the numerical workspace.  Production keeps
 * the hook disabled, while focused tests can force a partial allocation
 * failure and verify atomic belief publication and cleanup. */
static int64_t exact_test_alloc_fail_after = -1;

void osprey_exact_test_set_alloc_fail_after(int64_t allocations)
{
    exact_test_alloc_fail_after = allocations;
}

static bool exact_test_alloc_allowed(void)
{
    if (exact_test_alloc_fail_after < 0) return true;
    if (exact_test_alloc_fail_after == 0) return false;
    exact_test_alloc_fail_after--;
    return true;
}

static void *exact_try_malloc(size_t bytes)
{
    return exact_test_alloc_allowed() ? g_try_malloc(bytes) : NULL;
}

static void *exact_try_malloc0(size_t bytes)
{
    return exact_test_alloc_allowed() ? g_try_malloc0(bytes) : NULL;
}

/* A log-domain value is either finite or the exact representation of zero.
 * Positive infinity and NaN are never valid intermediate values. */
static bool exact_log_value_valid(double value)
{
    return isfinite(value) || value == -INFINITY;
}

bool osprey_exact_logaddexp(double left, double right, double *out)
{
    double high;
    double low;
    double value;

    if (out == NULL || !exact_log_value_valid(left) ||
        !exact_log_value_valid(right)) return false;
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
    if (!exact_log_value_valid(value)) return false;
    *out = value;
    return true;
}

/* Add two log weights belonging to one assignment.  This is ordinary
 * addition, not logaddexp: a -INFINITY term makes the product exactly zero. */
static bool exact_log_product_add(double left, double right, double *out)
{
    double value;

    if (out == NULL || !exact_log_value_valid(left) ||
        !exact_log_value_valid(right)) return false;
    if (left == -INFINITY || right == -INFINITY) {
        *out = -INFINITY;
        return true;
    }
    value = left + right;
    if (!exact_log_value_valid(value)) return false;
    *out = value;
    return true;
}

bool osprey_exact_log_normalize(double *table, size_t count,
                                double *log_norm)
{
    double norm = -INFINITY;

    if (table == NULL || count == 0 || log_norm == NULL) return false;
    for (size_t i = 0; i < count; i++) {
        if (!exact_log_value_valid(table[i]) ||
            !osprey_exact_logaddexp(norm, table[i], &norm)) return false;
    }
    if (norm == -INFINITY || !isfinite(norm)) return false;
    for (size_t i = 0; i < count; i++) {
        if (table[i] == -INFINITY) continue;
        table[i] -= norm;
        if (!exact_log_value_valid(table[i]) || table[i] > 0.0) {
            return false;
        }
    }
    *log_norm = norm;
    return true;
}

static bool exact_array_size(uint64_t count, size_t element_size,
                             size_t *bytes)
{
    if (bytes == NULL || element_size == 0 ||
        count > SIZE_MAX / element_size) return false;
    *bytes = (size_t)count * element_size;
    return true;
}

static bool exact_double_table_size(uint64_t cells, size_t *bytes)
{
    if (cells == 0 || !exact_array_size(cells, sizeof(double), bytes)) {
        return false;
    }
    return true;
}

static bool exact_message_index(const uint32_t *positions, uint32_t count,
                               uint64_t assignment, uint64_t cells,
                               uint64_t *out)
{
    uint64_t index = 0;

    if (positions == NULL || out == NULL || count >= sizeof(uint64_t) * 8u ||
        cells == 0) return false;
    for (uint32_t i = 0; i < count; i++) {
        uint32_t position = positions[i];
        if (position >= sizeof(uint64_t) * 8u) return false;
        if (((assignment >> position) & 1u) != 0) {
            index |= UINT64_C(1) << i;
        }
    }
    if (index >= cells) return false;
    *out = index;
    return true;
}

static void exact_numeric_workspace_free(OspreyExactNumericWorkspace *work)
{
    if (work == NULL) return;
    if (work->clique_potentials != NULL) {
        for (uint32_t i = 0; i < work->clique_count; i++) {
            g_free(work->clique_potentials[i]);
        }
    }
    if (work->messages != NULL) {
        for (uint32_t i = 0; i < work->edge_count; i++) {
            g_free(work->messages[i].parent_to_child);
            g_free(work->messages[i].child_to_parent);
        }
    }
    if (work->edge_maps != NULL) {
        for (uint32_t i = 0; i < work->edge_count; i++) {
            g_free(work->edge_maps[i].parent_positions);
            g_free(work->edge_maps[i].child_positions);
        }
    }
    g_free(work->clique_potentials);
    g_free(work->messages);
    g_free(work->edge_maps);
    g_free(work->parent_edge);
    g_free(work->preorder);
    memset(work, 0, sizeof(*work));
}

static bool exact_numeric_edge_map_build(
    const OspreyExactTopologyComponent *component,
    const OspreyExactTreeEdge *edge, OspreyExactNumericEdgeMap *map)
{
    OspreyExactClique *parent;
    OspreyExactClique *child;
    uint32_t count;
    size_t bytes;

    if (component == NULL || edge == NULL || map == NULL ||
        edge->parent >= component->cliques->len ||
        edge->child >= component->cliques->len ||
        edge->separator == NULL || edge->separator->len == 0) return false;
    parent = g_ptr_array_index(component->cliques, edge->parent);
    child = g_ptr_array_index(component->cliques, edge->child);
    count = edge->separator->len;
    if (!exact_array_size(count, sizeof(uint32_t), &bytes)) return false;
    map->count = count;
    map->parent_positions = exact_try_malloc(bytes);
    map->child_positions = exact_try_malloc(bytes);
    if (map->parent_positions == NULL || map->child_positions == NULL) {
        g_free(map->parent_positions);
        g_free(map->child_positions);
        map->parent_positions = NULL;
        map->child_positions = NULL;
        return false;
    }
    for (uint32_t i = 0; i < count; i++) {
        map->parent_positions[i] = UINT32_MAX;
        map->child_positions[i] = UINT32_MAX;
    }
    for (uint32_t i = 0; i < count; i++) {
        uint32_t local = g_array_index(edge->separator, uint32_t, i);
        uint32_t parent_position;
        uint32_t child_position;
        if (!exact_local_position(parent->local_vars, local,
                                  &parent_position) ||
            !exact_local_position(child->local_vars, local,
                                  &child_position)) return false;
        for (uint32_t j = 0; j < i; j++) {
            if (map->parent_positions[j] == parent_position ||
                map->child_positions[j] == child_position) return false;
        }
        map->parent_positions[i] = parent_position;
        map->child_positions[i] = child_position;
    }
    return true;
}

static bool exact_numeric_edge_before(
    const OspreyExactTopologyComponent *component, uint32_t left,
    uint32_t right)
{
    const OspreyExactTreeEdge *a;
    const OspreyExactTreeEdge *b;

    a = &g_array_index(component->tree_edges, OspreyExactTreeEdge, left);
    b = &g_array_index(component->tree_edges, OspreyExactTreeEdge, right);
    if (a->parent != b->parent) return a->parent < b->parent;
    if (a->child != b->child) return a->child < b->child;
    return left < right;
}

static bool exact_numeric_order_build(
    const OspreyExactTopologyComponent *component,
    OspreyExactNumericWorkspace *work)
{
    uint8_t *seen = NULL;
    size_t seen_bytes;
    uint32_t order_count = 0;

    if (component == NULL || work == NULL || component->cliques == NULL ||
        component->tree_edges == NULL || component->root_clique != 0 ||
        work->clique_count == 0 ||
        component->tree_edges->len + 1 != work->clique_count) return false;
    for (uint32_t i = 0; i < work->clique_count; i++) {
        work->parent_edge[i] = UINT32_MAX;
    }
    for (uint32_t i = 0; i < work->edge_count; i++) {
        const OspreyExactTreeEdge *edge = &g_array_index(
            component->tree_edges, OspreyExactTreeEdge, i);
        if (edge->parent >= work->clique_count ||
            edge->child >= work->clique_count || edge->parent == edge->child ||
            edge->child == 0 || work->parent_edge[edge->child] != UINT32_MAX) {
            return false;
        }
        work->parent_edge[edge->child] = i;
        work->preorder[i] = i;
    }
    for (uint32_t i = 1; i < work->edge_count; i++) {
        uint32_t value = work->preorder[i];
        uint32_t j = i;
        while (j != 0 && exact_numeric_edge_before(component, value,
                                                   work->preorder[j - 1])) {
            work->preorder[j] = work->preorder[j - 1];
            j--;
        }
        work->preorder[j] = value;
    }
    for (uint32_t i = 1; i < work->clique_count; i++) {
        if (work->parent_edge[i] == UINT32_MAX) return false;
    }

    if (!exact_array_size(work->clique_count, sizeof(*seen), &seen_bytes)) {
        return false;
    }
    seen = exact_try_malloc0(seen_bytes);
    if (seen == NULL) return false;
    work->preorder[0] = 0;
    seen[0] = 1;
    order_count = 1;
    for (uint32_t i = 0; i < order_count; i++) {
        uint32_t current = work->preorder[i];
        for (uint32_t j = 0; j < work->edge_count; j++) {
            const OspreyExactTreeEdge *edge = &g_array_index(
                component->tree_edges, OspreyExactTreeEdge, j);
            if (edge->parent != current || seen[edge->child]) continue;
            if (order_count >= work->clique_count) {
                g_free(seen);
                return false;
            }
            seen[edge->child] = 1;
            work->preorder[order_count++] = edge->child;
        }
    }
    g_free(seen);
    return order_count == work->clique_count;
}

static bool exact_numeric_workspace_init(
    const OspreyExactTopologyComponent *component,
    OspreyExactNumericWorkspace *work)
{
    if (component == NULL || work == NULL || component->cliques == NULL ||
        component->tree_edges == NULL || component->cliques->len == 0) {
        return false;
    }
    memset(work, 0, sizeof(*work));
    work->clique_count = component->cliques->len;
    work->edge_count = component->tree_edges->len;
    size_t clique_bytes;
    size_t parent_edge_bytes;
    size_t preorder_bytes;
    if (!exact_array_size(work->clique_count,
                          sizeof(*work->clique_potentials), &clique_bytes) ||
        !exact_array_size(work->clique_count, sizeof(*work->parent_edge),
                          &parent_edge_bytes) ||
        !exact_array_size(work->clique_count, sizeof(*work->preorder),
                          &preorder_bytes)) return false;
    work->clique_potentials = exact_try_malloc0(clique_bytes);
    work->parent_edge = exact_try_malloc(parent_edge_bytes);
    work->preorder = exact_try_malloc(preorder_bytes);
    if (work->clique_potentials == NULL || work->parent_edge == NULL ||
        work->preorder == NULL) return false;
    if (work->edge_count != 0) {
        size_t edge_bytes;
        if (!exact_array_size(work->edge_count, sizeof(*work->messages),
                              &edge_bytes)) return false;
        work->messages = exact_try_malloc0(edge_bytes);
        if (!exact_array_size(work->edge_count, sizeof(*work->edge_maps),
                              &edge_bytes)) return false;
        work->edge_maps = exact_try_malloc0(edge_bytes);
        if (work->messages == NULL || work->edge_maps == NULL) return false;
    }

    for (uint32_t i = 0; i < work->clique_count; i++) {
        const OspreyExactClique *clique = g_ptr_array_index(
            component->cliques, i);
        size_t bytes;
        if (clique == NULL ||
            !exact_double_table_size(clique->assignment_cells, &bytes)) {
            return false;
        }
        work->clique_potentials[i] = exact_try_malloc(bytes);
        if (work->clique_potentials[i] == NULL) return false;
        for (uint64_t j = 0; j < clique->assignment_cells; j++) {
            work->clique_potentials[i][(size_t)j] = 0.0;
        }
    }
    for (uint32_t i = 0; i < work->edge_count; i++) {
        const OspreyExactTreeEdge *edge = &g_array_index(
            component->tree_edges, OspreyExactTreeEdge, i);
        size_t bytes;
        if (!exact_double_table_size(edge->separator_cells, &bytes) ||
            !exact_numeric_edge_map_build(component, edge,
                                          &work->edge_maps[i])) return false;
        work->messages[i].cells = edge->separator_cells;
        work->messages[i].parent_to_child_log_norm = NAN;
        work->messages[i].child_to_parent_log_norm = NAN;
        work->messages[i].parent_to_child = exact_try_malloc(bytes);
        work->messages[i].child_to_parent = exact_try_malloc(bytes);
        if (work->messages[i].parent_to_child == NULL ||
            work->messages[i].child_to_parent == NULL) return false;
        for (uint64_t j = 0; j < edge->separator_cells; j++) {
            work->messages[i].parent_to_child[(size_t)j] = -INFINITY;
            work->messages[i].child_to_parent[(size_t)j] = -INFINITY;
        }
    }
    return exact_numeric_order_build(component, work);
}

/* Dense assignment convention: bit j is the Boolean state of the
 * sorted clique local_vars[j].  Separator bit j is separator[j], with
 * edge maps translating that canonical order at each endpoint. */
static bool exact_numeric_build_clique_potential(
    const OspreyGraph *graph, const OspreyExactBase *base,
    const OspreyExactTopologyComponent *component,
    const OspreyExactClique *clique, double *potential)
{
    if (graph == NULL || base == NULL || component == NULL || clique == NULL ||
        potential == NULL || clique->assignment_cells == 0) return false;
    for (guint i = 0; i < clique->factor_refs->len; i++) {
        uint32_t ref_id = g_array_index(clique->factor_refs, uint32_t, i);
        const OspreyExactFactorRef *ref;
        const OspreyFactor *factor;
        uint32_t positions[OSPREY_FACTOR_MAX_ARITY];
        if (ref_id >= base->factor_refs->len) return false;
        ref = &g_array_index(base->factor_refs, OspreyExactFactorRef,
                             ref_id);
        if (ref->graph_factor_id >= graph->factors->len ||
            ref->num_vars == 0 || ref->num_vars > OSPREY_FACTOR_MAX_ARITY) {
            return false;
        }
        factor = g_array_index(graph->factors, OspreyFactor *,
                               ref->graph_factor_id);
        if (factor == NULL || factor->num_vars != ref->num_vars) return false;
        for (uint32_t j = 0; j < ref->num_vars; j++) {
            positions[j] = UINT32_MAX;
            if (!exact_local_position(clique->local_vars,
                                      ref->local_vars[j], &positions[j]) ||
                positions[j] == UINT32_MAX) return false;
            for (uint32_t k = 0; k < j; k++) {
                if (positions[k] == positions[j]) return false;
            }
        }
        for (uint64_t assignment = 0;
             assignment < clique->assignment_cells; assignment++) {
            uint8_t factor_assignment[OSPREY_FACTOR_MAX_ARITY];
            double term;
            for (uint32_t j = 0; j < ref->num_vars; j++) {
                if (positions[j] >= sizeof(uint64_t) * 8u) return false;
                factor_assignment[j] = (uint8_t)((assignment >> positions[j]) &
                                                1u);
            }
            if (!osprey_factor_log_weight(factor, factor_assignment, &term) ||
                !exact_log_value_valid(term) ||
                !exact_log_product_add(potential[(size_t)assignment], term,
                                       &potential[(size_t)assignment])) {
                return false;
            }
        }
    }
    return true;
}

static bool exact_numeric_add_incoming(
    const OspreyExactTopologyComponent *component,
    const OspreyExactNumericWorkspace *work, uint32_t source,
    uint32_t excluded_edge, uint64_t assignment, double *value)
{
    for (uint32_t i = 0; i < work->edge_count; i++) {
        const OspreyExactTreeEdge *edge = &g_array_index(
            component->tree_edges, OspreyExactTreeEdge, i);
        const OspreyExactNumericEdgeMap *map = &work->edge_maps[i];
        const double *message;
        const uint32_t *positions;
        uint64_t index;

        if (i == excluded_edge ||
            (edge->parent != source && edge->child != source)) continue;
        if (edge->parent == source) {
            message = work->messages[i].child_to_parent;
            positions = map->parent_positions;
            if (!work->messages[i].child_to_parent_ready) return false;
        } else {
            message = work->messages[i].parent_to_child;
            positions = map->child_positions;
            if (!work->messages[i].parent_to_child_ready) return false;
        }
        if (message == NULL || !exact_message_index(
                positions, map->count, assignment, work->messages[i].cells,
                &index) ||
            !exact_log_product_add(*value, message[(size_t)index], value)) {
            return false;
        }
    }
    return true;
}

static OspreyStatus exact_numeric_compute_message(
    const OspreyExactTopologyComponent *component,
    OspreyExactNumericWorkspace *work, uint32_t edge_id,
    bool parent_to_child)
{
    const OspreyExactTreeEdge *edge;
    const OspreyExactNumericEdgeMap *map;
    OspreyExactNumericMessage *message;
    const OspreyExactClique *source_clique;
    const uint32_t *source_positions;
    double *output;
    bool *ready;
    double *published_log_norm;
    uint32_t source;
    uint32_t destination;
    uint64_t cells;
    double log_norm;

    if (component == NULL || work == NULL || edge_id >= work->edge_count) {
        return OSPREY_INVALID_GRAPH;
    }
    edge = &g_array_index(component->tree_edges, OspreyExactTreeEdge, edge_id);
    map = &work->edge_maps[edge_id];
    message = &work->messages[edge_id];
    source = parent_to_child ? edge->parent : edge->child;
    destination = parent_to_child ? edge->child : edge->parent;
    if (source >= work->clique_count || destination >= work->clique_count) {
        return OSPREY_INVALID_GRAPH;
    }
    source_clique = g_ptr_array_index(component->cliques, source);
    source_positions = parent_to_child ? map->parent_positions :
                                         map->child_positions;
    output = parent_to_child ? message->parent_to_child :
                               message->child_to_parent;
    ready = parent_to_child ? &message->parent_to_child_ready :
                              &message->child_to_parent_ready;
    published_log_norm = parent_to_child
        ? &message->parent_to_child_log_norm
        : &message->child_to_parent_log_norm;
    cells = message->cells;
    if (source_clique == NULL || source_positions == NULL || output == NULL ||
        *ready || cells == 0) return OSPREY_INVALID_GRAPH;
    for (uint64_t i = 0; i < cells; i++) output[(size_t)i] = -INFINITY;

    for (uint64_t assignment = 0;
         assignment < source_clique->assignment_cells; assignment++) {
        uint64_t index;
        double value = work->clique_potentials[source][(size_t)assignment];
        if (!exact_log_value_valid(value) ||
            !exact_numeric_add_incoming(component, work, source, edge_id,
                                        assignment, &value) ||
            !exact_message_index(source_positions, map->count, assignment,
                                 cells, &index) ||
            !osprey_exact_logaddexp(output[(size_t)index], value,
                                    &output[(size_t)index])) {
            return OSPREY_INVALID_GRAPH;
        }
    }
    if (!osprey_exact_log_normalize(output, (size_t)cells, &log_norm)) {
        return OSPREY_INVALID_MODEL;
    }
    *published_log_norm = log_norm;
    *ready = true;
    return OSPREY_OK;
}

static OspreyStatus exact_numeric_build_clique_belief(
    const OspreyExactTopologyComponent *component,
    const OspreyExactNumericWorkspace *work, uint32_t clique_id,
    double *belief, double *log_norm)
{
    const OspreyExactClique *clique;

    if (component == NULL || work == NULL || belief == NULL || log_norm == NULL ||
        clique_id >= work->clique_count) return OSPREY_INVALID_GRAPH;
    clique = g_ptr_array_index(component->cliques, clique_id);
    if (clique == NULL) return OSPREY_INVALID_GRAPH;
    for (uint64_t assignment = 0;
         assignment < clique->assignment_cells; assignment++) {
        double value = belief[(size_t)assignment];
        if (!exact_log_value_valid(value) ||
            !exact_numeric_add_incoming(component, work, clique_id,
                                        UINT32_MAX, assignment, &value)) {
            return OSPREY_INVALID_GRAPH;
        }
        belief[(size_t)assignment] = value;
    }
    return osprey_exact_log_normalize(belief,
                                      (size_t)clique->assignment_cells,
                                      log_norm)
        ? OSPREY_OK
        : OSPREY_INVALID_MODEL;
}

static bool exact_numeric_binary_marginal(const double *belief, uint64_t cells,
                                          uint32_t position, double *out)
{
    double zero = -INFINITY;
    double one = -INFINITY;
    double norm;
    double probability;

    if (belief == NULL || out == NULL || cells == 0 ||
        position >= sizeof(uint64_t) * 8u) return false;
    for (uint64_t assignment = 0; assignment < cells; assignment++) {
        double *accumulator = ((assignment >> position) & 1u) != 0
            ? &one : &zero;
        if (!osprey_exact_logaddexp(*accumulator,
                                     belief[(size_t)assignment],
                                     accumulator)) return false;
    }
    if (zero == -INFINITY && one == -INFINITY) return false;
    if (zero == -INFINITY) {
        *out = 1.0;
        return true;
    }
    if (one == -INFINITY) {
        *out = 0.0;
        return true;
    }
    if (!osprey_exact_logaddexp(zero, one, &norm) || !isfinite(norm)) {
        return false;
    }
    probability = exp(one - norm);
    if (!isfinite(probability) || probability < 0.0 || probability > 1.0) {
        return false;
    }
    *out = probability;
    return true;
}

static OspreyStatus exact_numeric_component(
    const OspreyGraph *graph, const OspreyExactBase *base,
    const OspreyExactTopologyComponent *component, double *marginals,
    double *logz_out)
{
    OspreyExactNumericWorkspace work;
    OspreyStatus status = OSPREY_INVALID_GRAPH;
    double root_log_norm = NAN;
    double logz;

    if (graph == NULL || base == NULL || component == NULL ||
        marginals == NULL || logz_out == NULL) return status;
    memset(&work, 0, sizeof(work));
    if (!exact_numeric_workspace_init(component, &work)) goto out;
    for (uint32_t i = 0; i < work.clique_count; i++) {
        const OspreyExactClique *clique = g_ptr_array_index(
            component->cliques, i);
        if (!exact_numeric_build_clique_potential(
                graph, base, component, clique, work.clique_potentials[i])) {
            goto out;
        }
    }

    /* The preorder is rooted at clique zero.  Reverse preorder is a
     * deterministic postorder for the child-to-parent pass. */
    for (uint32_t i = work.clique_count; i > 1; i--) {
        uint32_t clique = work.preorder[i - 1];
        uint32_t edge = work.parent_edge[clique];
        if (edge == UINT32_MAX) goto out;
        OspreyStatus message_status = exact_numeric_compute_message(
            component, &work, edge, false);
        if (message_status != OSPREY_OK) {
            status = message_status;
            goto out;
        }
    }
    for (uint32_t i = 1; i < work.clique_count; i++) {
        uint32_t clique = work.preorder[i];
        uint32_t edge = work.parent_edge[clique];
        if (edge == UINT32_MAX) goto out;
        OspreyStatus message_status = exact_numeric_compute_message(
            component, &work, edge, true);
        if (message_status != OSPREY_OK) {
            status = message_status;
            goto out;
        }
    }
    for (uint32_t i = 0; i < work.edge_count; i++) {
        if (!work.messages[i].parent_to_child_ready ||
            !work.messages[i].child_to_parent_ready ||
            !isfinite(work.messages[i].parent_to_child_log_norm) ||
            !isfinite(work.messages[i].child_to_parent_log_norm)) goto out;
    }

    /* Both message passes are complete, so no later operation needs the
     * uncalibrated clique potentials.  Reuse each planned dense table for its
     * normalized belief instead of allocating an unbudgeted duplicate. */
    for (uint32_t clique_id = 0; clique_id < work.clique_count; clique_id++) {
        const OspreyExactClique *clique = g_ptr_array_index(
            component->cliques, clique_id);
        double *belief = work.clique_potentials[clique_id];
        double clique_log_norm;
        OspreyStatus belief_status;
        if (clique == NULL || belief == NULL) goto out;
        belief_status = exact_numeric_build_clique_belief(
            component, &work, clique_id, belief, &clique_log_norm);
        if (belief_status != OSPREY_OK) {
            status = belief_status;
            goto out;
        }
        if (clique_id == 0) root_log_norm = clique_log_norm;
        for (guint position = 0; position < clique->local_vars->len;
             position++) {
            uint32_t local = g_array_index(clique->local_vars, uint32_t,
                                           position);
            double marginal;
            if (local >= base->graph_var_ids->len ||
                !exact_numeric_binary_marginal(belief,
                                               clique->assignment_cells,
                                               position, &marginal)) {
                status = OSPREY_INVALID_GRAPH;
                goto out;
            }
            if (isnan(marginals[local])) {
                marginals[local] = marginal;
            } else if (!isfinite(marginals[local]) ||
                       fabs(marginals[local] - marginal) >
                           OSPREY_EXACT_MARGINAL_TOL) {
                status = OSPREY_INVALID_GRAPH;
                goto out;
            }
        }
    }
    if (!isfinite(root_log_norm)) goto out;
    logz = root_log_norm;
    for (uint32_t i = 0; i < work.edge_count; i++) {
        if (!exact_log_product_add(logz,
                                   work.messages[i].child_to_parent_log_norm,
                                   &logz)) goto out;
    }
    if (!isfinite(logz)) goto out;
    *logz_out = logz;
    status = OSPREY_OK;
out:
    exact_numeric_workspace_free(&work);
    return status;
}

static OspreyStatus exact_numeric_infer(OspreyContext *ctx,
                                         const OspreyExactBase *base,
                                         const OspreyExactTopology *topology)
{
    uint32_t local_count;
    size_t marginal_bytes;
    double *marginals = NULL;
    double total_logz = 0.0;
    OspreyStatus status = OSPREY_INVALID_GRAPH;

    if (ctx == NULL || ctx->graph == NULL || base == NULL || topology == NULL ||
        topology->components == NULL ||
        topology->components->len != base->components->len ||
        base->graph_var_ids == NULL || base->local_by_graph == NULL) {
        return exact_projection_failure(ctx, status);
    }
    local_count = base->graph_var_ids->len;
    if (!exact_double_table_size(local_count, &marginal_bytes)) {
        return exact_projection_failure(ctx, status);
    }
    marginals = exact_try_malloc(marginal_bytes);
    if (marginals == NULL) goto out;
    for (uint32_t i = 0; i < local_count; i++) marginals[i] = NAN;

    for (guint i = 0; i < topology->components->len; i++) {
        const OspreyExactTopologyComponent *component = g_ptr_array_index(
            topology->components, i);
        double component_logz;
        OspreyStatus component_status = exact_numeric_component(
            ctx->graph, base, component, marginals, &component_logz);
        if (component_status != OSPREY_OK || !isfinite(component_logz) ||
            !isfinite(total_logz + component_logz)) {
            status = component_status == OSPREY_OK
                ? OSPREY_INVALID_GRAPH
                : component_status;
            goto out;
        }
        total_logz += component_logz;
    }
    for (uint32_t local = 0; local < local_count; local++) {
        if (!isfinite(marginals[local]) || marginals[local] < 0.0 ||
            marginals[local] > 1.0) goto out;
    }
    for (uint32_t graph_id = 0; graph_id < base->graph_var_count;
         graph_id++) {
        uint32_t local = base->local_by_graph[graph_id];
        if (local == UINT32_MAX) continue; /* secondary-only variable */
        if (local >= local_count ||
            g_array_index(ctx->graph->vars, OspreyVar, graph_id).id !=
                graph_id) goto out;
    }

    /* This is the only graph mutation in Stage 4.3.  All component tables,
     * messages, marginals, and log-partition values have succeeded above. */
    ctx->last_exact_logz = total_logz;
    for (uint32_t local = 0; local < local_count; local++) {
        uint32_t graph_id = g_array_index(base->graph_var_ids, uint32_t, local);
        g_array_index(ctx->graph->vars, OspreyVar, graph_id).belief =
            marginals[local];
    }
    status = OSPREY_OK;
out:
    g_free(marginals);
    return exact_projection_failure(ctx, status);
}

OspreyStatus osprey_stage4_exact(OspreyContext *ctx)
{
    OspreyExactBase *base = NULL;
    OspreyExactTopology *topology = NULL;
    OspreyStatus status;

    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    status = osprey_exact_base_build(ctx, &base);
    if (status != OSPREY_OK) return status;
    status = osprey_exact_topology_build(ctx, base, &topology);
    if (status != OSPREY_OK) {
        osprey_exact_base_free(base);
        return status;
    }
    status = exact_numeric_infer(ctx, base, topology);
    if (status == OSPREY_OK) {
        log_msg("[osprey] [infer] [exact] [components %u] [vars %u] "
                "[factors %u] [cliques %llu] [max-clique %llu] "
                "[table-bytes %llu]\n",
                topology->components->len, topology->variable_count,
                topology->factor_count,
                (unsigned long long)topology->clique_count,
                (unsigned long long)topology->max_clique_vars,
                (unsigned long long)topology->table_bytes);
    }
    osprey_exact_topology_free(topology);
    osprey_exact_base_free(base);
    return status;
}

/* ------------------------------------------------------------------ */
/* Loopy BP (log domain, synchronous, damped)                          */
/* ------------------------------------------------------------------ */

typedef struct OspEdge {
    uint32_t factor;      /* index into graph->factors */
    uint32_t var;         /* var id */
    uint32_t pos;         /* position of var within factor->var_ids */
    uint32_t next;        /* next edge id in the same ring */
} OspEdge;

typedef struct OspBp {
    OspreyGraph *g;
    GArray *edges;        /* OspEdge */
    uint32_t *var_ring;   /* var id -> head edge id (UINT32_MAX none) */
    uint32_t *fac_ring;   /* factor idx -> head edge id */
    double *msg_fv0, *msg_fv1;   /* factor -> variable log messages */
    double *msg_vf0, *msg_vf1;   /* variable -> factor log messages */
} OspBp;

static void bp_build(OspBp *bp, OspreyGraph *g) {
    memset(bp, 0, sizeof(*bp));
    bp->g = g;
    bp->edges = g_array_new(FALSE, FALSE, sizeof(OspEdge));
    bp->fac_ring = g_new(uint32_t, g->factors->len);
    bp->var_ring = g_new(uint32_t, g->vars->len);
    for (uint32_t f = 0; f < g->factors->len; f++) bp->fac_ring[f] = UINT32_MAX;
    for (uint32_t v = 0; v < g->vars->len; v++) bp->var_ring[v] = UINT32_MAX;
    for (guint fi = 0; fi < g->factors->len; fi++) {
        OspreyFactor *F = g_array_index(g->factors, OspreyFactor *, fi);
        for (uint32_t i = 0; i < F->num_vars; i++) {
            OspEdge e;
            e.factor = fi;
            e.var = F->var_ids[i];
            e.pos = i;
            e.next = bp->fac_ring[fi];
            g_array_append_val(bp->edges, e);
            bp->fac_ring[fi] = bp->edges->len - 1;
        }
    }
    for (guint i = 0; i < bp->edges->len; i++) {
        OspEdge *e = &g_array_index(bp->edges, OspEdge, i);
        e->next = bp->var_ring[e->var];
        bp->var_ring[e->var] = i;
    }
    uint32_t n = bp->edges->len;
    bp->msg_fv0 = g_new0(double, n);
    bp->msg_fv1 = g_new0(double, n);
    bp->msg_vf0 = g_new(double, n);
    bp->msg_vf1 = g_new(double, n);
    /* seed variable->factor messages from exact beliefs */
    for (uint32_t i = 0; i < n; i++) {
        OspEdge *e = &g_array_index(bp->edges, OspEdge, i);
        double b = g_array_index(g->vars, OspreyVar, e->var).belief;
        if (!(b > 0.0)) b = 0.5;
        if (b > 0.999999) b = 0.999999;
        if (b < 0.000001) b = 0.000001;
        bp->msg_vf0[i] = log(1.0 - b);
        bp->msg_vf1[i] = log(b);
    }
}

static void bp_free(OspBp *bp) {
    g_array_free(bp->edges, TRUE);
    g_free(bp->fac_ring);
    g_free(bp->var_ring);
    g_free(bp->msg_fv0);
    g_free(bp->msg_fv1);
    g_free(bp->msg_vf0);
    g_free(bp->msg_vf1);
}

/* Variable -> factor: sum of incoming factor logs. */
static void bp_var_to_factor(OspBp *bp, uint32_t edge) {
    OspEdge *e = &g_array_index(bp->edges, OspEdge, edge);
    double l0 = 0.0, l1 = 0.0;
    uint32_t ring = bp->var_ring[e->var];
    while (ring != UINT32_MAX) {
        if (ring != edge) {
            l0 += bp->msg_fv0[ring];
            l1 += bp->msg_fv1[ring];
        }
        ring = g_array_index(bp->edges, OspEdge, ring).next;
    }
    bp->msg_vf0[edge] = l0;
    bp->msg_vf1[edge] = l1;
}

/* Factor -> variable: eliminate the factor's other variables over its
 * table (k <= 8 by the factor-add cap). */
static void bp_factor_to_var(OspBp *bp, uint32_t edge) {
    OspEdge *e = &g_array_index(bp->edges, OspEdge, edge);
    OspreyFactor *f = g_array_index(bp->g->factors, OspreyFactor *,
                                    e->factor);
    uint32_t k = f->num_vars;
    uint32_t total = 1u << k;
    double in0[8], in1[8];
    for (uint32_t i = 0; i < k; i++) {
        in0[i] = in1[i] = 0.0;
        uint32_t ring = bp->fac_ring[e->factor];
        while (ring != UINT32_MAX) {
            OspEdge *o = &g_array_index(bp->edges, OspEdge, ring);
            if (o->pos == i) {
                in0[i] = bp->msg_vf0[ring];
                in1[i] = bp->msg_vf1[ring];
                break;
            }
            ring = o->next;
        }
    }
    double m0 = -INFINITY, m1 = -INFINITY;
    uint32_t bits[8];
    for (uint32_t a = 0; a < total; a++) {
        if (((a >> e->pos) & 1) != 0) continue;
        for (uint32_t i = 0; i < k; i++) bits[i] = (a >> i) & 1;
        double l = log(factor_value(f, bits));
        for (uint32_t i = 0; i < k; i++) l += (bits[i] ? in1[i] : in0[i]);
        if (l > m0) m0 = l;
    }
    for (uint32_t a = 0; a < total; a++) {
        if (((a >> e->pos) & 1) == 0) continue;
        for (uint32_t i = 0; i < k; i++) bits[i] = (a >> i) & 1;
        double l = log(factor_value(f, bits));
        for (uint32_t i = 0; i < k; i++) l += (bits[i] ? in1[i] : in0[i]);
        if (l > m1) m1 = l;
    }
    bp->msg_fv0[edge] = m0;
    bp->msg_fv1[edge] = m1;
}

static void bp_round(OspBp *bp) {
    for (guint i = 0; i < bp->edges->len; i++) bp_var_to_factor(bp, i);
    for (guint i = 0; i < bp->edges->len; i++) bp_factor_to_var(bp, i);
}

static double bp_belief(OspBp *bp, uint32_t var) {
    OspreyVar *v = &g_array_index(bp->g->vars, OspreyVar, var);
    if (v->hard_false) return 0.0;
    double l0 = 0.0, l1 = 0.0;
    uint32_t ring = bp->var_ring[var];
    while (ring != UINT32_MAX) {
        l0 += bp->msg_fv0[ring];
        l1 += bp->msg_fv1[ring];
        ring = g_array_index(bp->edges, OspEdge, ring).next;
    }
    double mx = l0 > l1 ? l0 : l1;
    double e0 = exp(l0 - mx), e1 = exp(l1 - mx);
    double s = e0 + e1;
    if (!(s > 0.0)) return 0.5;
    return e1 / s;
}

/* Damped synchronous BP; writes beliefs; returns (iters, converged). */
static bool bp_run(OspBp *bp, uint32_t max_iters, uint32_t *iters_out,
                   double *best_delta_out) {
    OspreyGraph *g = bp->g;
    double *prev = g_new(double, g->vars->len);
    for (uint32_t i = 0; i < g->vars->len; i++) {
        prev[i] = g_array_index(g->vars, OspreyVar, i).belief;
        if (!(prev[i] > 0.0)) prev[i] = 0.5;
    }
    double best_delta = INFINITY;
    uint32_t stable = 0;
    uint32_t iters = 0;
    bool converged = false;
    for (uint32_t it = 0; it < max_iters; it++) {
        iters = it + 1;
        bp_round(bp);
        /* damping: blend new messages with the previous iterate */
        double *old0 = g_new(double, bp->edges->len);
        double *old1 = g_new(double, bp->edges->len);
        memcpy(old0, bp->msg_fv0, bp->edges->len * sizeof(double));
        memcpy(old1, bp->msg_fv1, bp->edges->len * sizeof(double));
        for (guint i = 0; i < bp->edges->len; i++) {
            bp->msg_fv0[i] = OSPREY_BP_DAMPING * old0[i] +
                             (1.0 - OSPREY_BP_DAMPING) * bp->msg_fv0[i];
            bp->msg_fv1[i] = OSPREY_BP_DAMPING * old1[i] +
                             (1.0 - OSPREY_BP_DAMPING) * bp->msg_fv1[i];
        }
        g_free(old0);
        g_free(old1);
        double max_delta = 0.0;
        for (uint32_t v = 0; v < g->vars->len; v++) {
            double b = bp_belief(bp, v);
            g_array_index(g->vars, OspreyVar, v).belief = b;
            double d = fabs(b - prev[v]);
            if (d > max_delta) max_delta = d;
            prev[v] = b;
        }
        if (max_delta < best_delta) best_delta = max_delta;
        if (max_delta < OSPREY_BP_TOL) {
            stable++;
            if (stable >= OSPREY_BP_CONVERGED_ROUNDS) {
                converged = true;
                break;
            }
        } else {
            stable = 0;
        }
    }
    g_free(prev);
    *iters_out = iters;
    *best_delta_out = best_delta;
    return converged;
}

/* ------------------------------------------------------------------ */
/* CC07 heap folding closure                                           */
/* ------------------------------------------------------------------ */

static uint32_t cc07_fold_pass(OspreyContext *ctx) {
    OspreyGraph *g = ctx->graph;
    uint32_t created = 0;
    for (guint i = 0; i < g->vars->len; i++) {
        OspreyVar *u = &g_array_index(g->vars, OspreyVar, i);
        if (u->kind != OSPREY_PRED_UNFOLDABLE_HEAP) continue;
        if (u->belief <= 0.5) continue;
        uint64_t s_h = u->payload.heap_fold.size;
        for (guint j = 0; j < g->vars->len; j++) {
            OspreyVar *t = &g_array_index(g->vars, OspreyVar, j);
            if (t->kind != OSPREY_PRED_FOLDABLE_HEAP) continue;
            if (t->belief <= 0.5) continue;
            uint64_t s_t = t->payload.heap_fold.size;
            if (s_t == 0) continue;      /* CC07 guard */
            if (!region_eq(&u->payload.heap_fold.region,
                             &t->payload.heap_fold.region)) continue;
            int64_t tail_lo = (int64_t)(s_h + s_t);
            for (guint k = 0; k < g->vars->len; k++) {
                OspreyVar *v = &g_array_index(g->vars, OspreyVar, k);
                if (v->kind != OSPREY_PRED_PRIMITIVE_VAR) continue;
                const OspreyAddress *va = &v->payload.chunk.address;
                if (va->region.kind != OSPREY_REGION_HEAP_SITE) continue;
                if (!region_eq(&va->region,
                                 &u->payload.heap_fold.region)) continue;
                int64_t o = va->offset;
                if (o < tail_lo) continue;
                int64_t rel = o - (int64_t)s_h;
                int64_t mod = rel % (int64_t)s_t;
                int64_t fo = mod + (int64_t)s_h;
                if (fo == o) continue;
                OspreyChunk fc = v->payload.chunk;
                fc.address.offset = fo;
                OspreyVarPayload pv;
                memset(&pv, 0, sizeof(pv));
                pv.chunk = fc;
                uint32_t nv = osprey_intern_var_id(ctx,
                                                OSPREY_PRED_PRIMITIVE_VAR,
                                                &pv);
                if (nv == UINT32_MAX) continue;
                bool is_new = (nv == g->vars->len - 1);
                if (is_new) created++;
                uint32_t ids3[3] = { v->id, u->id, t->id };
                osprey_factor_add(ctx, OSPREY_RULE_CC07, 0, false,
                                  OSPREY_P_UP, ids3, 3);
                uint32_t ids2[2] = { nv, v->id };
                osprey_factor_add(ctx, OSPREY_RULE_CC07, 1, true,
                                  OSPREY_P_DN, ids2, 2);
            }
        }
    }
    return created;
}

/* ------------------------------------------------------------------ */
/* Stage-3 entry                                                       */
/* ------------------------------------------------------------------ */

OspreyStatus osprey_infer(OspreyContext *ctx) {
    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    if (ctx->graph == NULL || ctx->graph->vars->len == 0) {
        return OSPREY_INCOMPLETE_FACTS;
    }
    OspreyGraph *g = ctx->graph;

    /* Stage 4.3 computes exact base marginals.  The legacy secondary BP
     * path below remains explicitly untrusted and is retained only for
     * existing fail-closed integration behavior. */
    OspreyStatus exact_status = osprey_stage4_exact(ctx);
    if (exact_status != OSPREY_OK) return exact_status;

    /* Legacy Stage-5 placeholder: loopy BP with folding closure. */
    uint32_t fold_rounds = 0;
    bool converged = false;
    uint32_t iters = 0;
    double best_delta = INFINITY;
    for (;;) {
        OspBp bp;
        bp_build(&bp, g);
        converged = bp_run(&bp, OSPREY_BP_MAX_ITERS, &iters, &best_delta);
        bp_free(&bp);
        if (fold_rounds >= OSPREY_BP_MAX_FOLD_ROUNDS) break;
        uint32_t created = cc07_fold_pass(ctx);
        if (created == 0) break;
        fold_rounds++;
        log_msg("[osprey] [fold] [round %u] [new-vars %u]\n",
                fold_rounds, created);
    }

    uint32_t above = 0;
    for (uint32_t v = 0; v < g->vars->len; v++) {
        OspreyVar *var = &g_array_index(g->vars, OspreyVar, v);
        if (var->belief > 0.5) above++;
    }
    log_msg("[osprey] [infer] [bp] [iters %u] [converged %d] "
            "[best-delta %.3g] [belief>0.5 %u] [fold-rounds %u]\n",
            iters, converged ? 1 : 0, best_delta, above, fold_rounds);

    /* A limit/error raised during folding closure wins over the
     * convergence verdict (fail-closed transaction). */
    if (ctx->last_status != OSPREY_OK) {
        return ctx->last_status;
    }
    return converged ? OSPREY_OK : OSPREY_NON_CONVERGED;
}
