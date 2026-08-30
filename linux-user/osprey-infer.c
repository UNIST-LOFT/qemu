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

bool osprey_logaddexp(double left, double right, double *out)
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
bool osprey_log_product_add(double left, double right, double *out)
{
    double value;

    if (out == NULL || !exact_log_value_valid(left) ||
        !exact_log_value_valid(right)) return false;
    if (left == -INFINITY || right == -INFINITY) {
        *out = -INFINITY;
        return true;
    }
    value = left + right;
    /* Both inputs are finite here.  A non-finite sum is arithmetic
     * overflow, not exact zero support. */
    if (!isfinite(value)) return false;
    *out = value;
    return true;
}

bool osprey_log_normalize(double *table, size_t count,
                                double *log_norm)
{
    double norm = -INFINITY;

    if (table == NULL || count == 0 || log_norm == NULL) return false;
    for (size_t i = 0; i < count; i++) {
        if (!exact_log_value_valid(table[i]) ||
            !osprey_logaddexp(norm, table[i], &norm)) return false;
    }
    if (norm == -INFINITY || !isfinite(norm)) return false;
    for (size_t i = 0; i < count; i++) {
        double normalized;
        if (table[i] == -INFINITY) continue;
        normalized = table[i] - norm;
        /* A finite weight may not become exact zero through arithmetic
         * underflow; only an input -INFINITY represents hard zero. */
        if (!isfinite(normalized) || normalized > 0.0) return false;
        table[i] = normalized;
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
                !osprey_log_product_add(potential[(size_t)assignment], term,
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
            !osprey_log_product_add(*value, message[(size_t)index], value)) {
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
            !osprey_logaddexp(output[(size_t)index], value,
                                    &output[(size_t)index])) {
            return OSPREY_INVALID_GRAPH;
        }
    }
    if (!osprey_log_normalize(output, (size_t)cells, &log_norm)) {
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
    return osprey_log_normalize(belief,
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
        if (!osprey_logaddexp(*accumulator,
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
    if (!osprey_logaddexp(zero, one, &norm) || !isfinite(norm)) {
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
        if (!osprey_log_product_add(logz,
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
        OspreyVar *variable = &g_array_index(ctx->graph->vars, OspreyVar,
                                               graph_id);
        variable->belief = marginals[local];
        variable->belief_valid = 1;
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
/* Stage 5.1: canonical complete-graph projection                      */
/* ------------------------------------------------------------------ */

#define OSPREY_BP_DEFAULT_TABLE_BYTES (256ULL * 1024ULL * 1024ULL)

static int64_t bp_test_alloc_fail_after = -1;

void osprey_bp_test_set_alloc_fail_after(int64_t allocations)
{
    bp_test_alloc_fail_after = allocations;
}

static bool bp_alloc_allowed(void)
{
    if (bp_test_alloc_fail_after < 0) return true;
    if (bp_test_alloc_fail_after == 0) return false;
    bp_test_alloc_fail_after--;
    return true;
}

static void *bp_try_alloc(size_t size)
{
    if (!bp_alloc_allowed()) return NULL;
    if (size == 0) size = 1;
    return g_try_malloc(size);
}

static void *bp_try_alloc0(size_t size)
{
    void *memory = bp_try_alloc(size);
    if (memory != NULL) memset(memory, 0, size);
    return memory;
}

static bool bp_bytes_for(uint64_t count, size_t element_size,
                         uint64_t *out);

static GArray *bp_array_new(guint element_size, guint reserved)
{
    uint64_t bytes;
    if (!bp_bytes_for(reserved, element_size, &bytes) ||
        !bp_alloc_allowed()) return NULL;
    return g_array_sized_new(FALSE, FALSE, element_size, reserved);
}

static GPtrArray *bp_ptr_array_new(guint reserved)
{
    uint64_t bytes;
    if (!bp_bytes_for(reserved, sizeof(gpointer), &bytes) ||
        !bp_alloc_allowed()) return NULL;
    return g_ptr_array_sized_new(reserved);
}

static bool bp_u64_add(uint64_t *total, uint64_t value)
{
    if (total == NULL || value > SIZE_MAX || *total > SIZE_MAX - value ||
        UINT64_MAX - *total < value) return false;
    *total += value;
    return true;
}

static bool bp_u64_mul(uint64_t left, uint64_t right, uint64_t *out)
{
    if (out == NULL || (right != 0 && left > UINT64_MAX / right)) {
        return false;
    }
    *out = left * right;
    return true;
}

static bool bp_bytes_for(uint64_t count, size_t element_size,
                         uint64_t *out)
{
    return bp_u64_mul(count, (uint64_t)element_size, out) &&
           *out <= SIZE_MAX;
}

static bool bp_workspace_add(uint64_t *total, uint64_t count,
                             size_t element_size)
{
    uint64_t bytes;
    return bp_bytes_for(count, element_size, &bytes) &&
           bp_u64_add(total, bytes);
}

static int bp_factor_key_compare(const OspreyFactorKey *a,
                                 const OspreyFactorKey *b)
{
    int c;

    c = exact_cmp_u64(a->stage, b->stage);
    if (c != 0) return c;
    c = exact_cmp_u64(a->rule, b->rule);
    if (c != 0) return c;
    c = exact_cmp_u64(a->potential_kind, b->potential_kind);
    if (c != 0) return c;
    c = exact_cmp_u64(a->negative, b->negative);
    if (c != 0) return c;
    c = exact_cmp_u64(a->p_bits, b->p_bits);
    if (c != 0) return c;
    c = exact_cmp_u64(a->head_idx, b->head_idx);
    if (c != 0) return c;
    c = exact_cmp_u64(a->num_vars, b->num_vars);
    if (c != 0) return c;
    for (uint32_t i = 0; i < a->num_vars; i++) {
        c = exact_cmp_u64(a->var_ids[i], b->var_ids[i]);
        if (c != 0) return c;
    }
    return 0;
}

static int bp_edge_key_compare(const OspreyBpEdgeKey *a,
                               const OspreyBpEdgeKey *b)
{
    int c = bp_factor_key_compare(&a->factor, &b->factor);
    if (c != 0) return c;
    c = exact_cmp_u64(a->factor_position, b->factor_position);
    return c != 0 ? c : exact_key_compare(&a->variable, &b->variable);
}

static bool bp_rule_stage_valid(const OspreyFactor *factor)
{
    bool base;
    bool secondary;

    if (factor == NULL) return false;
    base = factor->rule >= OSPREY_RULE_CA01 &&
           factor->rule <= OSPREY_RULE_CA08;
    secondary = (factor->rule >= OSPREY_RULE_CB01 &&
                 factor->rule <= OSPREY_RULE_CB09) ||
                (factor->rule >= OSPREY_RULE_CC01 &&
                 factor->rule <= OSPREY_RULE_CC07) ||
                (factor->rule >= OSPREY_RULE_CD01 &&
                 factor->rule <= OSPREY_RULE_CD08) ||
                factor->rule == OSPREY_RULE_CD10 ||
                factor->rule == OSPREY_RULE_CD11;
    return (factor->stage == OSPREY_GRAPH_BASE_CA && base) ||
           (factor->stage == OSPREY_GRAPH_SECONDARY && secondary);
}

static bool bp_source_factor_valid(const OspreyFactor *factor,
                                   const OspreyGraph *graph)
{
    return factor != NULL && graph != NULL && bp_rule_stage_valid(factor) &&
           exact_factor_valid(factor, graph);
}

typedef struct OspreyBpVarBuild {
    OspreyKey key;
    OspreyVarPayload payload;
    uint32_t graph_var_id;
    uint8_t kind;
} OspreyBpVarBuild;

typedef struct OspreyBpFactorBuild {
    OspreyFactorKey key;
    uint32_t graph_factor_id;
} OspreyBpFactorBuild;

typedef struct OspreyBpComponentCounts {
    uint32_t vars;
    uint32_t factors;
    uint32_t edges;
} OspreyBpComponentCounts;

static int bp_var_build_compare(const void *ap, const void *bp)
{
    const OspreyBpVarBuild *a = ap;
    const OspreyBpVarBuild *b = bp;
    int c = exact_cmp_u64(a->kind, b->kind);

    if (c == 0) c = osprey_var_payload_compare(a->kind, &a->payload,
                                                &b->payload);
    if (c == 0) c = exact_key_compare(&a->key, &b->key);
    if (c == 0) c = exact_cmp_u64(a->graph_var_id, b->graph_var_id);
    return c;
}

static int bp_factor_build_compare(const void *ap, const void *bp)
{
    const OspreyBpFactorBuild *a = ap;
    const OspreyBpFactorBuild *b = bp;
    int c = bp_factor_key_compare(&a->key, &b->key);

    return c != 0 ? c : exact_cmp_u64(a->graph_factor_id,
                                       b->graph_factor_id);
}

static OspreyFactorKey bp_factor_semantic_key(const OspreyFactor *factor,
                                              const uint32_t *local_by_graph)
{
    OspreyFactorKey key;
    uint64_t p_bits;

    memset(&key, 0, sizeof(key));
    key.rule = factor->rule;
    key.stage = factor->stage;
    key.potential_kind = factor->potential_kind;
    key.negative = factor->negative;
    key.head_idx = factor->head_idx;
    memcpy(&p_bits, &factor->p, sizeof(p_bits));
    key.p_bits = p_bits;
    key.num_vars = factor->num_vars;
    for (uint32_t i = 0; i < factor->num_vars; i++) {
        key.var_ids[i] = local_by_graph[factor->var_ids[i]];
    }
    return key;
}

static uint64_t bp_workspace_limit(const OspreyConfig *config)
{
    if (config == NULL || config->max_bp_table_bytes == 0) {
        return OSPREY_BP_DEFAULT_TABLE_BYTES;
    }
    return config->max_bp_table_bytes;
}

static bool bp_graph_workspace_bytes(const OspreyBpGraph *graph,
                                     uint64_t *out)
{
    uint64_t total = 0;
    uint64_t message_values;

    if (graph == NULL || out == NULL || graph->vars == NULL ||
        graph->factors == NULL || graph->edges == NULL ||
        graph->var_edges == NULL || graph->components == NULL ||
        graph->local_by_graph_var == NULL ||
        graph->local_by_graph_factor == NULL) {
        return false;
    }
    if (!bp_u64_add(&total, sizeof(*graph)) ||
        !bp_u64_add(&total, 4u * sizeof(GArray)) ||
        !bp_u64_add(&total, sizeof(GPtrArray)) ||
        !bp_workspace_add(&total, graph->vars->len, sizeof(OspreyBpVarRef)) ||
        !bp_workspace_add(&total, graph->factors->len,
                          sizeof(OspreyBpFactorRef)) ||
        !bp_workspace_add(&total, graph->edges->len, sizeof(OspreyBpEdge)) ||
        !bp_workspace_add(&total, graph->var_edges->len, sizeof(uint32_t)) ||
        !bp_workspace_add(&total, graph->vars->len, sizeof(uint32_t)) ||
        !bp_workspace_add(&total, graph->factors->len, sizeof(uint32_t)) ||
        !bp_workspace_add(&total, graph->components->len,
                          sizeof(gpointer))) {
        return false;
    }
    message_values = (uint64_t)graph->edges->len * 2u;
    if (!bp_workspace_add(&total, message_values, sizeof(double)) ||
        !bp_workspace_add(&total, message_values, sizeof(double)) ||
        !bp_workspace_add(&total, message_values, sizeof(double)) ||
        !bp_workspace_add(&total, message_values, sizeof(double)) ||
        !bp_workspace_add(&total, message_values, sizeof(double)) ||
        !bp_workspace_add(&total, (uint64_t)graph->vars->len * 2u,
                          sizeof(double))) {
        return false;
    }
    for (guint i = 0; i < graph->components->len; i++) {
        const OspreyBpComponent *component = g_ptr_array_index(
            graph->components, i);
        if (component == NULL || component->local_vars == NULL ||
            component->local_factors == NULL || component->edges == NULL ||
            !bp_u64_add(&total, sizeof(*component)) ||
            !bp_u64_add(&total, 3u * sizeof(GArray)) ||
            !bp_workspace_add(&total, component->local_vars->len,
                              sizeof(uint32_t)) ||
            !bp_workspace_add(&total, component->local_factors->len,
                              sizeof(uint32_t)) ||
            !bp_workspace_add(&total, component->edges->len,
                              sizeof(uint32_t))) {
            return false;
        }
    }
    *out = total;
    return true;
}

static void bp_component_free(OspreyBpComponent *component)
{
    if (component == NULL) return;
    if (component->local_vars != NULL) g_array_free(component->local_vars, TRUE);
    if (component->local_factors != NULL) {
        g_array_free(component->local_factors, TRUE);
    }
    if (component->edges != NULL) g_array_free(component->edges, TRUE);
    g_free(component);
}

void osprey_bp_graph_free(OspreyBpGraph *graph)
{
    if (graph == NULL) return;
    if (graph->components != NULL) {
        for (guint i = 0; i < graph->components->len; i++) {
            bp_component_free(g_ptr_array_index(graph->components, i));
        }
        g_ptr_array_free(graph->components, TRUE);
    }
    if (graph->vars != NULL) g_array_free(graph->vars, TRUE);
    if (graph->factors != NULL) g_array_free(graph->factors, TRUE);
    if (graph->edges != NULL) g_array_free(graph->edges, TRUE);
    if (graph->var_edges != NULL) g_array_free(graph->var_edges, TRUE);
    g_free(graph->local_by_graph_var);
    g_free(graph->local_by_graph_factor);
    g_free(graph->msg_vf_current);
    g_free(graph->msg_vf_next);
    g_free(graph->msg_fv_current);
    g_free(graph->msg_fv_next);
    g_free(graph->scratch_message);
    g_free(graph->beliefs);
    g_free(graph);
}

static OspreyStatus bp_build_failure(OspreyContext *ctx,
                                     OspreyStatus status,
                                     const char *reason)
{
    if (ctx != NULL && (ctx->last_status == OSPREY_OK ||
                        ctx->last_status == OSPREY_DISABLED)) {
        ctx->last_status = status;
    }
    log_msg("[osprey] [infer] [bp] [stage 5.1] [reject] [reason %s]\n",
            reason == NULL ? "unknown" : reason);
    return status;
}

static bool bp_log_probability(double probability, double *out)
{
    if (out == NULL || !isfinite(probability) || probability < 0.0 ||
        probability > 1.0) return false;
    if (probability == 0.0) {
        *out = -INFINITY;
    } else if (probability == 1.0) {
        *out = 0.0;
    } else {
        *out = log(probability);
    }
    return true;
}

static bool bp_log_pair_valid(double zero, double one)
{
    double maximum;
    double sum;

    if ((!isfinite(zero) && !(zero == -INFINITY)) ||
        (!isfinite(one) && !(one == -INFINITY)) ||
        (zero == -INFINITY && one == -INFINITY)) return false;
    maximum = zero > one ? zero : one;
    sum = exp(zero - maximum) + exp(one - maximum);
    if (!(sum > 0.0) || !isfinite(sum)) return false;
    return fabs(maximum + log(sum)) <= 1e-12;
}

static void bp_expected_message(const OspreyBpVarRef *variable,
                                double *zero, double *one)
{
    double values[2];

    if (variable->base_seed_valid) {
        values[0] = variable->base_seed[0];
        values[1] = variable->base_seed[1];
    } else {
        values[0] = 0.5;
        values[1] = 0.5;
    }
    bp_log_probability(values[0], zero);
    bp_log_probability(values[1], one);
}

static bool bp_var_edges_sorted(const OspreyBpGraph *graph, uint32_t begin,
                                uint32_t count)
{
    /* Edges are created in canonical factor order and each valid factor names
     * a variable at most once.  Filtering that sequence into each variable's
     * CSR range therefore preserves the required edge-key order in O(E). */
    for (uint32_t i = 1; i < count; i++) {
        uint32_t previous = g_array_index(graph->var_edges, uint32_t,
                                          begin + i - 1);
        uint32_t current = g_array_index(graph->var_edges, uint32_t,
                                         begin + i);
        const OspreyBpEdge *a = &g_array_index(graph->edges, OspreyBpEdge,
                                               previous);
        const OspreyBpEdge *b = &g_array_index(graph->edges, OspreyBpEdge,
                                               current);
        if (bp_edge_key_compare(&a->key, &b->key) >= 0) return false;
    }
    return true;
}

OspreyStatus osprey_bp_graph_build(OspreyContext *ctx,
                                   OspreyBpGraph **out)
{
    OspreyGraph *source;
    OspreyBpGraph *graph = NULL;
    OspreyBpVarBuild *var_builds = NULL;
    OspreyBpFactorBuild *factor_builds = NULL;
    uint32_t *var_cursor = NULL;
    uint32_t *var_component = NULL;
    uint32_t *factor_component = NULL;
    uint32_t *var_queue = NULL;
    uint32_t *factor_queue = NULL;
    OspreyBpComponentCounts *component_counts = NULL;
    OspreyStatus status = OSPREY_INVALID_GRAPH;
    const char *reason = "malformed graph";
    uint32_t variable_count;
    uint32_t factor_count;
    uint32_t edge_count = 0;
    uint32_t component_count = 0;
    uint64_t bytes;
    uint64_t workspace;

    if (out != NULL) *out = NULL;
    if (ctx == NULL || out == NULL || !ctx->config.enabled ||
        ctx->graph == NULL) {
        return bp_build_failure(ctx,
                                ctx != NULL && !ctx->config.enabled
                                    ? OSPREY_DISABLED
                                    : OSPREY_INVALID_GRAPH,
                                "missing or disabled graph");
    }
    source = ctx->graph;
    if (source->vars == NULL || source->factors == NULL) {
        return bp_build_failure(ctx, OSPREY_INVALID_GRAPH,
                                "missing graph arrays");
    }
    if (source->vars->data == NULL || source->factors->data == NULL) {
        return bp_build_failure(ctx, OSPREY_INVALID_GRAPH,
                                "missing graph array storage");
    }
    if (source->vars->len == 0 || source->factors->len == 0) {
        return bp_build_failure(ctx, OSPREY_INVALID_GRAPH, "empty graph");
    }
    if (source->vars->len > UINT32_MAX ||
        source->factors->len > UINT32_MAX) {
        return bp_build_failure(ctx, OSPREY_LIMIT_EXCEEDED,
                                "graph count overflow");
    }
    variable_count = source->vars->len;
    factor_count = source->factors->len;
    if ((ctx->config.max_variables != 0 &&
         variable_count > ctx->config.max_variables) ||
        (ctx->config.max_factors != 0 && factor_count > ctx->config.max_factors)) {
        return bp_build_failure(ctx, OSPREY_LIMIT_EXCEEDED,
                                "graph count limit");
    }

    graph = bp_try_alloc0(sizeof(*graph));
    if (graph == NULL) {
        reason = "allocation graph";
        goto fail;
    }
    graph->workspace_limit = bp_workspace_limit(&ctx->config);
    graph->message_state = OSPREY_BP_MESSAGES_INITIAL;
    memset(graph->reserved_state, 0, sizeof(graph->reserved_state));
    graph->vars = bp_array_new(sizeof(OspreyBpVarRef), variable_count);
    if (graph->vars == NULL) {
        reason = "allocation variable references";
        goto fail;
    }
    if (!bp_bytes_for(variable_count, sizeof(*var_builds), &bytes)) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "variable projection size overflow";
        goto fail;
    }
    var_builds = bp_try_alloc(bytes);
    if (var_builds == NULL) {
        reason = "allocation variable ordering";
        goto fail;
    }
    if (!bp_bytes_for(variable_count, sizeof(uint32_t), &bytes)) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "variable map size overflow";
        goto fail;
    }
    graph->local_by_graph_var = bp_try_alloc(bytes);
    if (graph->local_by_graph_var == NULL) {
        reason = "allocation variable map";
        goto fail;
    }
    for (uint32_t i = 0; i < variable_count; i++) {
        graph->local_by_graph_var[i] = UINT32_MAX;
        OspreyVar *variable = &g_array_index(source->vars, OspreyVar, i);
        if (variable->id != i || variable->kind <= OSPREY_PRED_NONE ||
            variable->kind >= OSPREY_PRED_COUNT || variable->hard_false > 1 ||
            variable->region_limit_hit > 1 || variable->belief_valid > 1 ||
            !exact_payload_valid(variable->kind, &variable->payload)) {
            reason = "invalid variable";
            goto fail;
        }
        var_builds[i].kind = variable->kind;
        var_builds[i].payload = variable->payload;
        var_builds[i].graph_var_id = i;
        var_builds[i].key = osprey_var_key(variable->kind,
                                            &variable->payload);
    }
    qsort(var_builds, variable_count, sizeof(*var_builds),
          bp_var_build_compare);
    for (uint32_t local = 0; local < variable_count; local++) {
        OspreyBpVarRef ref;
        const OspreyBpVarBuild *ordered = &var_builds[local];
        OspreyVar *variable = &g_array_index(source->vars, OspreyVar,
                                             ordered->graph_var_id);
        memset(&ref, 0, sizeof(ref));
        if (local != 0 && exact_key_compare(&var_builds[local - 1].key,
                                            &ordered->key) == 0) {
            reason = "duplicate semantic variable";
            goto fail;
        }
        graph->local_by_graph_var[ordered->graph_var_id] = local;
        ref.graph_var_id = ordered->graph_var_id;
        ref.base_seed_valid = variable->belief_valid;
        if (ref.base_seed_valid) {
            if (!isfinite(variable->belief) || variable->belief < 0.0 ||
                variable->belief > 1.0) {
                reason = "invalid base belief";
                goto fail;
            }
            ref.base_seed[1] = variable->belief;
            ref.base_seed[0] = 1.0 - variable->belief;
            if (!isfinite(ref.base_seed[0])) {
                reason = "invalid base seed";
                goto fail;
            }
        } else {
            ref.base_seed[0] = NAN;
            ref.base_seed[1] = NAN;
        }
        g_array_append_val(graph->vars, ref);
    }

    if (!bp_bytes_for(factor_count, sizeof(*factor_builds), &bytes)) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "factor projection size overflow";
        goto fail;
    }
    factor_builds = bp_try_alloc(bytes);
    if (factor_builds == NULL) {
        reason = "allocation factor ordering";
        goto fail;
    }
    if (!bp_bytes_for(factor_count, sizeof(uint32_t), &bytes)) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "factor map size overflow";
        goto fail;
    }
    graph->local_by_graph_factor = bp_try_alloc(bytes);
    if (graph->local_by_graph_factor == NULL) {
        reason = "allocation factor map";
        goto fail;
    }
    for (uint32_t i = 0; i < factor_count; i++) {
        OspreyFactor *factor = g_array_index(source->factors,
                                             OspreyFactor *, i);
        if (factor == NULL || factor->id != i ||
            !bp_source_factor_valid(factor, source)) {
            reason = "invalid factor";
            goto fail;
        }
        for (uint32_t j = 0; j < factor->num_vars; j++) {
            if (factor->var_ids[j] >= variable_count ||
                graph->local_by_graph_var[factor->var_ids[j]] == UINT32_MAX) {
                reason = "factor variable map";
                goto fail;
            }
        }
        factor_builds[i].graph_factor_id = i;
        factor_builds[i].key = bp_factor_semantic_key(
            factor, graph->local_by_graph_var);
        if (factor->num_vars > UINT32_MAX - edge_count) {
            status = OSPREY_LIMIT_EXCEEDED;
            reason = "edge count overflow";
            goto fail;
        }
        edge_count += factor->num_vars;
    }
    if (edge_count == 0) {
        reason = "factorless graph";
        goto fail;
    }
    qsort(factor_builds, factor_count, sizeof(*factor_builds),
          bp_factor_build_compare);
    for (uint32_t i = 1; i < factor_count; i++) {
        if (bp_factor_key_compare(&factor_builds[i - 1].key,
                                  &factor_builds[i].key) == 0) {
            reason = "duplicate semantic factor";
            goto fail;
        }
    }
    graph->factors = bp_array_new(sizeof(OspreyBpFactorRef), factor_count);
    graph->edges = bp_array_new(sizeof(OspreyBpEdge), edge_count);
    graph->var_edges = bp_array_new(sizeof(uint32_t), edge_count);
    if (graph->factors == NULL || graph->edges == NULL ||
        graph->var_edges == NULL) {
        reason = "allocation adjacency records";
        goto fail;
    }
    for (uint32_t local_factor = 0; local_factor < factor_count;
         local_factor++) {
        const OspreyBpFactorBuild *ordered = &factor_builds[local_factor];
        OspreyFactor *factor = g_array_index(source->factors,
                                             OspreyFactor *,
                                             ordered->graph_factor_id);
        OspreyBpFactorRef ref;
        memset(&ref, 0, sizeof(ref));
        ref.graph_factor_id = ordered->graph_factor_id;
        ref.factor_edge_begin = graph->edges->len;
        ref.factor_edge_count = factor->num_vars;
        graph->local_by_graph_factor[ordered->graph_factor_id] = local_factor;
        g_array_append_val(graph->factors, ref);
        for (uint32_t position = 0; position < factor->num_vars; position++) {
            uint32_t graph_var_id = factor->var_ids[position];
            uint32_t local_var = graph->local_by_graph_var[graph_var_id];
            const OspreyVar *variable = &g_array_index(source->vars,
                                                       OspreyVar,
                                                       graph_var_id);
            OspreyBpEdge edge;
            memset(&edge, 0, sizeof(edge));
            edge.id = graph->edges->len;
            edge.local_var = local_var;
            edge.local_factor = local_factor;
            edge.factor_position = position;
            edge.graph_var_id = graph_var_id;
            edge.graph_factor_id = ordered->graph_factor_id;
            edge.key.factor = ordered->key;
            edge.key.variable = osprey_var_key(variable->kind,
                                                &variable->payload);
            edge.key.factor_position = position;
            g_array_append_val(graph->edges, edge);
        }
    }
    if (!bp_bytes_for(variable_count, sizeof(uint32_t), &bytes)) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "adjacency cursor size overflow";
        goto fail;
    }
    var_cursor = bp_try_alloc0(bytes);
    if (var_cursor == NULL) {
        reason = "allocation variable adjacency cursor";
        goto fail;
    }
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        OspreyBpEdge *edge = &g_array_index(graph->edges, OspreyBpEdge,
                                            edge_id);
        OspreyBpVarRef *variable = &g_array_index(graph->vars,
                                                  OspreyBpVarRef,
                                                  edge->local_var);
        if (variable->var_edge_count == UINT32_MAX) {
            status = OSPREY_LIMIT_EXCEEDED;
            reason = "variable adjacency count overflow";
            goto fail;
        }
        variable->var_edge_count++;
    }
    uint32_t var_edge_begin = 0;
    for (uint32_t local = 0; local < variable_count; local++) {
        OspreyBpVarRef *variable = &g_array_index(graph->vars,
                                                  OspreyBpVarRef, local);
        if (variable->var_edge_count == 0) {
            reason = "factorless variable";
            goto fail;
        }
        if (var_edge_begin > edge_count - variable->var_edge_count) {
            status = OSPREY_LIMIT_EXCEEDED;
            reason = "variable adjacency range overflow";
            goto fail;
        }
        variable->var_edge_begin = var_edge_begin;
        var_cursor[local] = var_edge_begin;
        var_edge_begin += variable->var_edge_count;
    }
    if (var_edge_begin != edge_count) {
        reason = "variable adjacency population";
        goto fail;
    }
    g_array_set_size(graph->var_edges, edge_count);
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        const OspreyBpEdge *edge = &g_array_index(graph->edges, OspreyBpEdge,
                                                  edge_id);
        g_array_index(graph->var_edges, uint32_t,
                      var_cursor[edge->local_var]++) = edge_id;
    }
    for (uint32_t local = 0; local < variable_count; local++) {
        const OspreyBpVarRef *variable = &g_array_index(graph->vars,
                                                        OspreyBpVarRef,
                                                        local);
        if (!bp_var_edges_sorted(graph, variable->var_edge_begin,
                                 variable->var_edge_count)) {
            reason = "variable adjacency order";
            goto fail;
        }
    }
    g_free(var_cursor);
    var_cursor = NULL;

    if (!bp_bytes_for(variable_count, sizeof(uint32_t), &bytes)) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "component map size overflow";
        goto fail;
    }
    var_component = bp_try_alloc(bytes);
    if (!bp_bytes_for(factor_count, sizeof(uint32_t), &bytes)) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "component factor map size overflow";
        goto fail;
    }
    factor_component = bp_try_alloc(bytes);
    if (!bp_bytes_for(variable_count, sizeof(uint32_t), &bytes)) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "component variable queue size overflow";
        goto fail;
    }
    var_queue = bp_try_alloc(bytes);
    if (!bp_bytes_for(factor_count, sizeof(uint32_t), &bytes)) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "component factor queue size overflow";
        goto fail;
    }
    factor_queue = bp_try_alloc(bytes);
    if (var_component == NULL || factor_component == NULL ||
        var_queue == NULL || factor_queue == NULL) {
        reason = "allocation component traversal";
        goto fail;
    }
    for (uint32_t i = 0; i < variable_count; i++) var_component[i] = UINT32_MAX;
    for (uint32_t i = 0; i < factor_count; i++) factor_component[i] = UINT32_MAX;
    for (uint32_t start = 0; start < variable_count; start++) {
        if (var_component[start] != UINT32_MAX) continue;
        if (component_count == UINT32_MAX) {
            status = OSPREY_LIMIT_EXCEEDED;
            reason = "component count overflow";
            goto fail;
        }
        uint32_t v_head = 0, v_tail = 0, f_head = 0, f_tail = 0;
        uint32_t component = component_count++;
        var_component[start] = component;
        var_queue[v_tail++] = start;
        while (v_head < v_tail || f_head < f_tail) {
            while (v_head < v_tail) {
                uint32_t local_var = var_queue[v_head++];
                const OspreyBpVarRef *variable = &g_array_index(
                    graph->vars, OspreyBpVarRef, local_var);
                for (uint32_t i = 0; i < variable->var_edge_count; i++) {
                    uint32_t edge_id = g_array_index(
                        graph->var_edges, uint32_t,
                        variable->var_edge_begin + i);
                    const OspreyBpEdge *edge = &g_array_index(
                        graph->edges, OspreyBpEdge, edge_id);
                    if (factor_component[edge->local_factor] == UINT32_MAX) {
                        factor_component[edge->local_factor] = component;
                        factor_queue[f_tail++] = edge->local_factor;
                    } else if (factor_component[edge->local_factor] !=
                               component) {
                        reason = "inconsistent factor component";
                        goto fail;
                    }
                }
            }
            while (f_head < f_tail) {
                uint32_t local_factor = factor_queue[f_head++];
                const OspreyBpFactorRef *factor = &g_array_index(
                    graph->factors, OspreyBpFactorRef, local_factor);
                for (uint32_t i = 0; i < factor->factor_edge_count; i++) {
                    uint32_t edge_id = factor->factor_edge_begin + i;
                    const OspreyBpEdge *edge = &g_array_index(
                        graph->edges, OspreyBpEdge, edge_id);
                    if (var_component[edge->local_var] == UINT32_MAX) {
                        var_component[edge->local_var] = component;
                        var_queue[v_tail++] = edge->local_var;
                    } else if (var_component[edge->local_var] != component) {
                        reason = "inconsistent variable component";
                        goto fail;
                    }
                }
            }
        }
    }
    if (component_count == 0) {
        reason = "empty component partition";
        goto fail;
    }
    if (!bp_bytes_for(component_count, sizeof(*component_counts), &bytes)) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "component count size overflow";
        goto fail;
    }
    component_counts = bp_try_alloc0(bytes);
    if (component_counts == NULL) {
        reason = "allocation component counts";
        goto fail;
    }
    for (uint32_t local = 0; local < variable_count; local++) {
        component_counts[var_component[local]].vars++;
    }
    for (uint32_t local = 0; local < factor_count; local++) {
        component_counts[factor_component[local]].factors++;
    }
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        const OspreyBpEdge *edge = &g_array_index(graph->edges, OspreyBpEdge,
                                                  edge_id);
        component_counts[factor_component[edge->local_factor]].edges++;
    }
    graph->components = bp_ptr_array_new(component_count);
    if (graph->components == NULL) {
        reason = "allocation component index";
        goto fail;
    }
    for (uint32_t component = 0; component < component_count; component++) {
        OspreyBpComponent *owned = bp_try_alloc0(sizeof(*owned));
        if (owned == NULL) {
            reason = "allocation component";
            goto fail;
        }
        owned->id = component;
        owned->local_vars = bp_array_new(sizeof(uint32_t),
                                         component_counts[component].vars);
        owned->local_factors = bp_array_new(
            sizeof(uint32_t), component_counts[component].factors);
        owned->edges = bp_array_new(sizeof(uint32_t),
                                    component_counts[component].edges);
        if (owned->local_vars == NULL || owned->local_factors == NULL ||
            owned->edges == NULL) {
            bp_component_free(owned);
            reason = "allocation component adjacency";
            goto fail;
        }
        g_ptr_array_add(graph->components, owned);
    }
    for (uint32_t local = 0; local < variable_count; local++) {
        OspreyBpComponent *component = g_ptr_array_index(
            graph->components, var_component[local]);
        g_array_append_val(component->local_vars, local);
    }
    for (uint32_t local = 0; local < factor_count; local++) {
        OspreyBpComponent *component = g_ptr_array_index(
            graph->components, factor_component[local]);
        g_array_append_val(component->local_factors, local);
    }
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        const OspreyBpEdge *edge = &g_array_index(graph->edges, OspreyBpEdge,
                                                  edge_id);
        OspreyBpComponent *component = g_ptr_array_index(
            graph->components, factor_component[edge->local_factor]);
        g_array_append_val(component->edges, edge_id);
    }
    for (uint32_t component = 0; component < component_count; component++) {
        OspreyBpComponent *owned = g_ptr_array_index(graph->components,
                                                     component);
        if (owned->local_vars->len == 0 || owned->local_factors->len == 0 ||
            owned->edges->len == 0) {
            reason = "empty bipartite component";
            goto fail;
        }
    }
    g_free(component_counts);
    component_counts = NULL;
    g_free(var_component);
    var_component = NULL;
    g_free(factor_component);
    factor_component = NULL;
    g_free(var_queue);
    var_queue = NULL;
    g_free(factor_queue);
    factor_queue = NULL;

    if (!bp_graph_workspace_bytes(graph, &workspace)) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "workspace size overflow";
        goto fail;
    }
    graph->workspace_bytes = workspace;
    if (workspace > graph->workspace_limit) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "BP workspace limit";
        goto fail;
    }
    if (!bp_bytes_for((uint64_t)edge_count * 2u, sizeof(double), &bytes)) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "message size overflow";
        goto fail;
    }
    graph->message_values = (uint64_t)edge_count * 2u;
    graph->msg_vf_current = bp_try_alloc(bytes);
    graph->msg_vf_next = bp_try_alloc(bytes);
    graph->msg_fv_current = bp_try_alloc(bytes);
    graph->msg_fv_next = bp_try_alloc(bytes);
    graph->scratch_message = bp_try_alloc(bytes);
    if (!bp_bytes_for((uint64_t)variable_count * 2u, sizeof(double), &bytes)) {
        status = OSPREY_LIMIT_EXCEEDED;
        reason = "belief size overflow";
        goto fail;
    }
    graph->beliefs = bp_try_alloc(bytes);
    if (graph->msg_vf_current == NULL || graph->msg_vf_next == NULL ||
        graph->msg_fv_current == NULL || graph->msg_fv_next == NULL ||
        graph->scratch_message == NULL || graph->beliefs == NULL) {
        reason = "allocation BP messages";
        goto fail;
    }
    for (uint64_t i = 0; i < graph->message_values; i++) {
        graph->msg_fv_current[i] = -log(2.0);
        graph->msg_vf_next[i] = NAN;
        graph->msg_fv_next[i] = NAN;
        graph->scratch_message[i] = NAN;
    }
    for (uint64_t i = 0; i < (uint64_t)variable_count * 2u; i++) {
        graph->beliefs[i] = NAN;
    }
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        const OspreyBpEdge *edge = &g_array_index(graph->edges, OspreyBpEdge,
                                                  edge_id);
        const OspreyBpVarRef *variable = &g_array_index(
            graph->vars, OspreyBpVarRef, edge->local_var);
        double zero, one;
        bp_expected_message(variable, &zero, &one);
        graph->msg_vf_current[(size_t)edge_id * 2u] = zero;
        graph->msg_vf_current[(size_t)edge_id * 2u + 1u] = one;
    }
    g_free(var_builds);
    g_free(factor_builds);
    *out = graph;
    return OSPREY_OK;

fail:
    g_free(var_builds);
    g_free(factor_builds);
    g_free(var_cursor);
    g_free(var_component);
    g_free(factor_component);
    g_free(var_queue);
    g_free(factor_queue);
    g_free(component_counts);
    osprey_bp_graph_free(graph);
    return bp_build_failure(ctx, status, reason);
}

bool osprey_bp_graph_validate(const OspreyContext *ctx,
                              const OspreyBpGraph *graph)
{
    const OspreyGraph *source;
    uint32_t variable_count;
    uint32_t factor_count;
    uint32_t edge_count;
    uint8_t *edge_seen = NULL;
    uint8_t *var_seen = NULL;
    uint8_t *factor_seen = NULL;
    uint32_t *component_parent = NULL;
    uint64_t workspace;
    uint32_t expected_begin = 0;
    bool valid = false;

    if (ctx == NULL || graph == NULL || !ctx->config.enabled ||
        ctx->graph == NULL || graph->vars == NULL || graph->factors == NULL ||
        graph->edges == NULL || graph->var_edges == NULL ||
        graph->components == NULL || graph->local_by_graph_var == NULL ||
        graph->local_by_graph_factor == NULL || graph->vars->data == NULL ||
        graph->factors->data == NULL || graph->edges->data == NULL ||
        graph->var_edges->data == NULL || graph->components->pdata == NULL ||
        graph->msg_vf_current == NULL || graph->msg_vf_next == NULL ||
        graph->msg_fv_current == NULL || graph->msg_fv_next == NULL ||
        graph->scratch_message == NULL || graph->beliefs == NULL ||
        graph->message_state > OSPREY_BP_MESSAGES_ITERATED ||
        memcmp(graph->reserved_state, (uint8_t[7]){ 0 },
               sizeof(graph->reserved_state)) != 0) return false;
    source = ctx->graph;
    if (source->vars == NULL || source->factors == NULL ||
        source->vars->data == NULL || source->factors->data == NULL ||
        source->vars->len == 0 || source->factors->len == 0 ||
        source->vars->len > UINT32_MAX || source->factors->len > UINT32_MAX ||
        graph->vars->len != source->vars->len ||
        graph->factors->len != source->factors->len ||
        graph->var_edges->len != graph->edges->len) return false;
    variable_count = source->vars->len;
    factor_count = source->factors->len;
    if (graph->edges->len > UINT32_MAX) return false;
    edge_count = graph->edges->len;
    if ((ctx->config.max_variables != 0 &&
         variable_count > ctx->config.max_variables) ||
        (ctx->config.max_factors != 0 &&
         factor_count > ctx->config.max_factors)) return false;
    if (graph->message_values != (uint64_t)edge_count * 2u ||
        graph->workspace_limit != bp_workspace_limit(&ctx->config) ||
        !bp_graph_workspace_bytes(graph, &workspace) ||
        workspace != graph->workspace_bytes ||
        workspace > graph->workspace_limit) return false;

    for (uint32_t local = 0; local < variable_count; local++) {
        const OspreyBpVarRef *ref = &g_array_index(graph->vars,
                                                   OspreyBpVarRef, local);
        const OspreyVar *variable;
        OspreyKey key;
        if (ref->graph_var_id >= variable_count ||
            graph->local_by_graph_var[ref->graph_var_id] != local ||
            ref->var_edge_begin > edge_count ||
            ref->var_edge_count > edge_count - ref->var_edge_begin ||
            ref->reserved[0] != 0 || ref->reserved[1] != 0 ||
            ref->reserved[2] != 0) return false;
        variable = &g_array_index(source->vars, OspreyVar, ref->graph_var_id);
        if (variable->id != ref->graph_var_id || variable->hard_false > 1 ||
            variable->region_limit_hit > 1 || variable->belief_valid > 1 ||
            ref->base_seed_valid > 1 ||
            !exact_payload_valid(variable->kind, &variable->payload)) return false;
        key = osprey_var_key(variable->kind, &variable->payload);
        if (local != 0) {
            const OspreyBpVarRef *previous = &g_array_index(
                graph->vars, OspreyBpVarRef, local - 1);
            const OspreyVar *previous_var = &g_array_index(
                source->vars, OspreyVar, previous->graph_var_id);
            int order = exact_cmp_u64(previous_var->kind, variable->kind);
            if (order == 0) {
                order = osprey_var_payload_compare(previous_var->kind,
                                                   &previous_var->payload,
                                                   &variable->payload);
            }
            if (order >= 0) return false;
        }
        if (ref->base_seed_valid > 1) return false;
        if (ref->base_seed_valid) {
            if (!isfinite(ref->base_seed[0]) ||
                !isfinite(ref->base_seed[1]) ||
                ref->base_seed[0] < 0.0 || ref->base_seed[1] < 0.0 ||
                ref->base_seed[0] > 1.0 || ref->base_seed[1] > 1.0 ||
                ref->base_seed[0] != 1.0 - ref->base_seed[1]) return false;
            if (graph->message_state == OSPREY_BP_MESSAGES_INITIAL &&
                (ref->base_seed_valid != variable->belief_valid ||
                 !isfinite(variable->belief) || variable->belief < 0.0 ||
                 variable->belief > 1.0 ||
                 ref->base_seed[1] != variable->belief ||
                 ref->base_seed[0] != 1.0 - variable->belief)) {
                return false;
            }
        } else if (!isnan(ref->base_seed[0]) ||
                   !isnan(ref->base_seed[1])) {
            return false;
        } else if (graph->message_state == OSPREY_BP_MESSAGES_INITIAL &&
                   variable->belief_valid != 0) {
            return false;
        }
        if (local != 0) {
            const OspreyBpVarRef *previous = &g_array_index(
                graph->vars, OspreyBpVarRef, local - 1);
            const OspreyVar *previous_var = &g_array_index(
                source->vars, OspreyVar, previous->graph_var_id);
            OspreyKey previous_key = osprey_var_key(previous_var->kind,
                                                    &previous_var->payload);
            /* OspreyKey is an equality key; signed offsets must be ordered
             * by the payload comparator above, not as unsigned key words. */
            if (exact_key_compare(&previous_key, &key) == 0) return false;
        }
    }
    for (uint32_t graph_id = 0; graph_id < variable_count; graph_id++) {
        if (graph->local_by_graph_var[graph_id] == UINT32_MAX ||
            graph->local_by_graph_var[graph_id] >= variable_count) return false;
    }
    for (uint32_t local = 0; local < factor_count; local++) {
        const OspreyBpFactorRef *ref = &g_array_index(
            graph->factors, OspreyBpFactorRef, local);
        OspreyFactor *factor;
        OspreyFactorKey key;
        if (ref->graph_factor_id >= factor_count ||
            graph->local_by_graph_factor[ref->graph_factor_id] != local ||
            ref->factor_edge_begin != expected_begin ||
            expected_begin > edge_count ||
            ref->factor_edge_count > edge_count - expected_begin) return false;
        factor = g_array_index(source->factors, OspreyFactor *,
                               ref->graph_factor_id);
        if (factor == NULL || factor->id != ref->graph_factor_id ||
            !bp_source_factor_valid(factor, source) ||
            ref->factor_edge_count != factor->num_vars) return false;
        key = bp_factor_semantic_key(factor, graph->local_by_graph_var);
        if (local != 0) {
            const OspreyBpFactorRef *previous = &g_array_index(
                graph->factors, OspreyBpFactorRef, local - 1);
            OspreyFactor *previous_factor = g_array_index(
                source->factors, OspreyFactor *, previous->graph_factor_id);
            OspreyFactorKey previous_key = bp_factor_semantic_key(
                previous_factor, graph->local_by_graph_var);
            if (bp_factor_key_compare(&previous_key, &key) >= 0) return false;
        }
        expected_begin += ref->factor_edge_count;
    }
    if (expected_begin != edge_count) return false;
    for (uint32_t graph_id = 0; graph_id < factor_count; graph_id++) {
        if (graph->local_by_graph_factor[graph_id] == UINT32_MAX ||
            graph->local_by_graph_factor[graph_id] >= factor_count) return false;
    }
    edge_seen = g_try_malloc0(edge_count);
    var_seen = g_try_malloc0(variable_count);
    factor_seen = g_try_malloc0(factor_count);
    component_parent = g_try_malloc((size_t)variable_count *
                                    sizeof(*component_parent));
    if (edge_seen == NULL || var_seen == NULL || factor_seen == NULL ||
        component_parent == NULL) goto out;
    for (uint32_t local = 0; local < variable_count; local++) {
        component_parent[local] = local;
    }
    for (uint32_t local_factor = 0; local_factor < factor_count;
         local_factor++) {
        const OspreyBpFactorRef *ref = &g_array_index(
            graph->factors, OspreyBpFactorRef, local_factor);
        OspreyFactor *factor = g_array_index(source->factors,
                                             OspreyFactor *,
                                             ref->graph_factor_id);
        for (uint32_t position = 0; position < ref->factor_edge_count;
             position++) {
            uint32_t edge_id = ref->factor_edge_begin + position;
            const OspreyBpEdge *edge;
            const OspreyVar *variable;
            OspreyBpEdgeKey expected_key;
            if (edge_id >= edge_count || edge_seen[edge_id]) goto out;
            edge_seen[edge_id] = 1;
            edge = &g_array_index(graph->edges, OspreyBpEdge, edge_id);
            if (edge->id != edge_id || edge->local_factor != local_factor ||
                edge->factor_position != position ||
                edge->graph_factor_id != ref->graph_factor_id ||
                edge->key.reserved != 0 ||
                edge->key.factor.reserved != 0 ||
                edge->key.factor.reserved2 != 0 ||
                edge->graph_var_id >= variable_count ||
                edge->local_var != graph->local_by_graph_var[
                    edge->graph_var_id] ||
                factor->var_ids[position] != edge->graph_var_id) goto out;
            variable = &g_array_index(source->vars, OspreyVar,
                                      edge->graph_var_id);
            memset(&expected_key, 0, sizeof(expected_key));
            expected_key.factor = bp_factor_semantic_key(
                factor, graph->local_by_graph_var);
            expected_key.variable = osprey_var_key(variable->kind,
                                                   &variable->payload);
            expected_key.factor_position = position;
            if (bp_edge_key_compare(&edge->key, &expected_key) != 0) goto out;
            if (position != 0) {
                const OspreyBpEdge *first = &g_array_index(
                    graph->edges, OspreyBpEdge, ref->factor_edge_begin);
                exact_uf_union(component_parent, first->local_var,
                               edge->local_var);
            }
        }
    }
    memset(edge_seen, 0, edge_count);
    for (uint32_t local_var = 0; local_var < variable_count; local_var++) {
        const OspreyBpVarRef *ref = &g_array_index(graph->vars,
                                                   OspreyBpVarRef, local_var);
        const OspreyBpEdge *previous = NULL;
        if (ref->var_edge_count == 0) goto out;
        if (local_var != 0) {
            const OspreyBpVarRef *prior = &g_array_index(
                graph->vars, OspreyBpVarRef, local_var - 1);
            if (ref->var_edge_begin != prior->var_edge_begin +
                                      prior->var_edge_count) goto out;
        } else if (ref->var_edge_begin != 0) {
            goto out;
        }
        for (uint32_t i = 0; i < ref->var_edge_count; i++) {
            uint32_t edge_id = g_array_index(graph->var_edges, uint32_t,
                                             ref->var_edge_begin + i);
            const OspreyBpEdge *edge;
            if (edge_id >= edge_count || edge_seen[edge_id]) goto out;
            edge_seen[edge_id] = 1;
            edge = &g_array_index(graph->edges, OspreyBpEdge, edge_id);
            if (edge->local_var != local_var ||
                (previous != NULL && bp_edge_key_compare(&previous->key,
                                                          &edge->key) >= 0)) {
                goto out;
            }
            previous = edge;
        }
    }
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        if (!edge_seen[edge_id]) goto out;
    }
    memset(edge_seen, 0, edge_count);
    for (guint component_id = 0; component_id < graph->components->len;
         component_id++) {
        const OspreyBpComponent *component = g_ptr_array_index(
            graph->components, component_id);
        uint32_t component_root = UINT32_MAX;
        if (component == NULL || component->id != component_id ||
            component->local_vars == NULL || component->local_factors == NULL ||
            component->edges == NULL || component->local_vars->data == NULL ||
            component->local_factors->data == NULL ||
            component->edges->data == NULL || component->local_vars->len == 0 ||
            component->local_factors->len == 0 || component->edges->len == 0) {
            goto out;
        }
        if (component_id != 0) {
            const OspreyBpComponent *previous = g_ptr_array_index(
                graph->components, component_id - 1);
            if (previous->local_vars->len == 0 ||
                g_array_index(previous->local_vars, uint32_t, 0) >=
                    g_array_index(component->local_vars, uint32_t, 0)) goto out;
        }
        for (guint i = 0; i < component->local_vars->len; i++) {
            uint32_t local = g_array_index(component->local_vars, uint32_t, i);
            if (local >= variable_count || var_seen[local] ||
                (i != 0 && g_array_index(component->local_vars, uint32_t,
                                         i - 1) >= local)) goto out;
            uint32_t root = exact_uf_find(component_parent, local);
            if (component_root == UINT32_MAX) {
                component_root = root;
            } else if (component_root != root) {
                goto out;
            }
            var_seen[local] = 1;
        }
        for (guint i = 0; i < component->local_factors->len; i++) {
            uint32_t local = g_array_index(component->local_factors, uint32_t, i);
            if (local >= factor_count || factor_seen[local] ||
                (i != 0 && g_array_index(component->local_factors, uint32_t,
                                         i - 1) >= local)) goto out;
            factor_seen[local] = 1;
        }
        for (guint i = 0; i < component->edges->len; i++) {
            uint32_t edge_id = g_array_index(component->edges, uint32_t, i);
            const OspreyBpEdge *edge;
            if (edge_id >= edge_count || edge_seen[edge_id] ||
                (i != 0 && g_array_index(component->edges, uint32_t,
                                         i - 1) >= edge_id)) goto out;
            edge_seen[edge_id] = 1;
            edge = &g_array_index(graph->edges, OspreyBpEdge, edge_id);
            bool found_var = false, found_factor = false;
            for (guint j = 0; j < component->local_vars->len; j++) {
                if (g_array_index(component->local_vars, uint32_t, j) ==
                    edge->local_var) {
                    found_var = true;
                    break;
                }
            }
            for (guint j = 0; j < component->local_factors->len; j++) {
                if (g_array_index(component->local_factors, uint32_t, j) ==
                    edge->local_factor) {
                    found_factor = true;
                    break;
                }
            }
            if (!found_var || !found_factor) goto out;
        }
    }
    for (uint32_t local = 0; local < variable_count; local++) {
        if (!var_seen[local]) goto out;
    }
    for (uint32_t local = 0; local < factor_count; local++) {
        if (!factor_seen[local]) goto out;
    }
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        if (!edge_seen[edge_id]) goto out;
    }
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        const double *vf = &graph->msg_vf_current[(size_t)edge_id * 2u];
        const double *fv = &graph->msg_fv_current[(size_t)edge_id * 2u];
        const OspreyBpEdge *edge = &g_array_index(graph->edges,
                                                  OspreyBpEdge, edge_id);
        const OspreyBpVarRef *variable = &g_array_index(
            graph->vars, OspreyBpVarRef, edge->local_var);
        double expected_zero, expected_one;
        if (!bp_log_pair_valid(vf[0], vf[1]) ||
            !bp_log_pair_valid(fv[0], fv[1])) goto out;
        if (graph->message_state == OSPREY_BP_MESSAGES_INITIAL) {
            bp_expected_message(variable, &expected_zero, &expected_one);
            if (fv[0] != -log(2.0) || fv[1] != -log(2.0) ||
                vf[0] != expected_zero || vf[1] != expected_one) goto out;
        }
    }
    for (uint64_t i = 0; i < graph->message_values; i++) {
        if (!isnan(graph->msg_vf_next[i]) ||
            !isnan(graph->msg_fv_next[i]) ||
            !isnan(graph->scratch_message[i])) goto out;
    }
    if (graph->message_state == OSPREY_BP_MESSAGES_INITIAL) {
        for (uint64_t i = 0; i < (uint64_t)variable_count * 2u; i++) {
            if (!isnan(graph->beliefs[i])) goto out;
        }
    } else {
        for (uint64_t i = 0; i < (uint64_t)variable_count * 2u; i++) {
            if (!isfinite(graph->beliefs[i]) || graph->beliefs[i] < 0.0 ||
                graph->beliefs[i] > 1.0) goto out;
        }
    }
    valid = true;
out:
    g_free(edge_seen);
    g_free(var_seen);
    g_free(factor_seen);
    g_free(component_parent);
    return valid;
}

static void bp_dump_key(FILE *out, const OspreyKey *key)
{
    fprintf(out, "%016llx", (unsigned long long)key->tag);
    for (size_t i = 0; i < G_N_ELEMENTS(key->w); i++) {
        fprintf(out, " %016llx", (unsigned long long)key->w[i]);
    }
}

static void bp_dump_factor_key(FILE *out, const OspreyFactorKey *key)
{
    fprintf(out, "%u %u %u %u %016llx %u %u",
            key->stage, key->rule, key->potential_kind, key->negative,
            (unsigned long long)key->p_bits, key->head_idx,
            key->num_vars);
    for (uint32_t i = 0; i < key->num_vars; i++) {
        fprintf(out, " %u", key->var_ids[i]);
    }
}

static void bp_dump_double_bits(FILE *out, double value)
{
    uint64_t bits;
    memcpy(&bits, &value, sizeof(bits));
    fprintf(out, "%016llx", (unsigned long long)bits);
}

bool osprey_bp_graph_dump_file(const OspreyContext *ctx,
                               const OspreyBpGraph *graph, FILE *out)
{
    if (ctx == NULL || graph == NULL || out == NULL ||
        !osprey_bp_graph_validate(ctx, graph)) return false;
    fprintf(out, "BP 1\nVARS %u\n", graph->vars->len);
    for (guint local = 0; local < graph->vars->len; local++) {
        const OspreyBpVarRef *ref = &g_array_index(graph->vars,
                                                   OspreyBpVarRef, local);
        const OspreyVar *variable = &g_array_index(
            ctx->graph->vars, OspreyVar, ref->graph_var_id);
        OspreyKey key = osprey_var_key(variable->kind, &variable->payload);
        fprintf(out, "V %u %u %u %u ", local, variable->kind,
                ref->var_edge_begin, ref->var_edge_count);
        bp_dump_key(out, &key);
        fprintf(out, " seed %u ", ref->base_seed_valid);
        bp_dump_double_bits(out, ref->base_seed[0]);
        fputc(' ', out);
        bp_dump_double_bits(out, ref->base_seed[1]);
        fputc('\n', out);
    }
    fprintf(out, "FACTORS %u\n", graph->factors->len);
    for (guint local = 0; local < graph->factors->len; local++) {
        const OspreyBpFactorRef *ref = &g_array_index(
            graph->factors, OspreyBpFactorRef, local);
        const OspreyFactor *factor = g_array_index(
            ctx->graph->factors, OspreyFactor *, ref->graph_factor_id);
        OspreyFactorKey key = bp_factor_semantic_key(
            factor, graph->local_by_graph_var);
        fprintf(out, "F %u %u %u ", local, ref->factor_edge_begin,
                ref->factor_edge_count);
        bp_dump_factor_key(out, &key);
        fputc('\n', out);
    }
    fprintf(out, "EDGES %u\n", graph->edges->len);
    for (guint edge_id = 0; edge_id < graph->edges->len; edge_id++) {
        const OspreyBpEdge *edge = &g_array_index(graph->edges,
                                                  OspreyBpEdge, edge_id);
        fprintf(out, "E %u %u %u ", edge->id, edge->local_var,
                edge->local_factor);
        bp_dump_factor_key(out, &edge->key.factor);
        fputc(' ', out);
        bp_dump_key(out, &edge->key.variable);
        fputc('\n', out);
    }
    fprintf(out, "VAR_EDGES %u\n", graph->var_edges->len);
    for (guint i = 0; i < graph->var_edges->len; i++) {
        fprintf(out, "%u %u\n", i,
                g_array_index(graph->var_edges, uint32_t, i));
    }
    fprintf(out, "COMPONENTS %u\n", graph->components->len);
    for (guint i = 0; i < graph->components->len; i++) {
        const OspreyBpComponent *component = g_ptr_array_index(
            graph->components, i);
        fprintf(out, "C %u v", component->id);
        for (guint j = 0; j < component->local_vars->len; j++) {
            fprintf(out, " %u", g_array_index(component->local_vars,
                                                uint32_t, j));
        }
        fprintf(out, " f");
        for (guint j = 0; j < component->local_factors->len; j++) {
            fprintf(out, " %u", g_array_index(component->local_factors,
                                                uint32_t, j));
        }
        fprintf(out, " e");
        for (guint j = 0; j < component->edges->len; j++) {
            fprintf(out, " %u", g_array_index(component->edges, uint32_t, j));
        }
        fputc('\n', out);
    }
    fprintf(out, "MESSAGES %llu WORKSPACE %llu\n",
            (unsigned long long)graph->message_values,
            (unsigned long long)graph->workspace_bytes);
    for (uint32_t edge_id = 0; edge_id < graph->edges->len; edge_id++) {
        size_t index = (size_t)edge_id * 2u;
        fprintf(out, "M %u vf ", edge_id);
        bp_dump_double_bits(out, graph->msg_vf_current[index]);
        fputc(' ', out);
        bp_dump_double_bits(out, graph->msg_vf_current[index + 1u]);
        fprintf(out, " fv ");
        bp_dump_double_bits(out, graph->msg_fv_current[index]);
        fputc(' ', out);
        bp_dump_double_bits(out, graph->msg_fv_current[index + 1u]);
        fputc('\n', out);
    }
    return !ferror(out);
}

/* ------------------------------------------------------------------ */
/* Stage 5.2: one-round normalized sum-product                         */
/* ------------------------------------------------------------------ */

static void bp_round_clear_next(OspreyBpMessages *messages,
                                uint64_t value_count)
{
    if (messages == NULL || messages->vf_next == NULL ||
        messages->fv_next == NULL) return;
    for (uint64_t i = 0; i < value_count; i++) {
        messages->vf_next[(size_t)i] = NAN;
        messages->fv_next[(size_t)i] = NAN;
    }
}

/* Validate only the immutable projection needed by the round.  The full
 * Stage-5.1 validator also checks construction-time seeds and empty scratch
 * buffers; those conditions are intentionally not required after a caller
 * has completed and swapped a round. */
static bool bp_round_graph_valid(const OspreyContext *ctx,
                                 const OspreyBpGraph *graph,
                                 uint32_t *edge_count_out)
{
    const OspreyGraph *source;
    uint32_t variable_count;
    uint32_t factor_count;
    uint32_t edge_count;
    uint32_t expected_begin = 0;
    uint32_t expected_var_begin = 0;

    if (ctx == NULL || graph == NULL || !ctx->config.enabled ||
        ctx->graph == NULL || graph->vars == NULL || graph->factors == NULL ||
        graph->edges == NULL || graph->var_edges == NULL ||
        graph->local_by_graph_var == NULL ||
        graph->local_by_graph_factor == NULL || graph->vars->data == NULL ||
        graph->factors->data == NULL || graph->edges->data == NULL ||
        graph->var_edges->data == NULL || edge_count_out == NULL ||
        graph->message_state > OSPREY_BP_MESSAGES_ITERATED ||
        memcmp(graph->reserved_state, (uint8_t[7]){ 0 },
               sizeof(graph->reserved_state)) != 0) {
        return false;
    }
    source = ctx->graph;
    if (source->vars == NULL || source->factors == NULL ||
        source->vars->data == NULL || source->factors->data == NULL ||
        source->vars->len == 0 || source->factors->len == 0 ||
        source->vars->len > UINT32_MAX || source->factors->len > UINT32_MAX ||
        graph->vars->len != source->vars->len ||
        graph->factors->len != source->factors->len ||
        graph->var_edges->len != graph->edges->len ||
        graph->edges->len == 0 || graph->edges->len > UINT32_MAX) {
        return false;
    }
    variable_count = source->vars->len;
    factor_count = source->factors->len;
    edge_count = graph->edges->len;

    for (uint32_t local = 0; local < variable_count; local++) {
        const OspreyBpVarRef *ref = &g_array_index(
            graph->vars, OspreyBpVarRef, local);
        const OspreyVar *variable;

        if (ref->graph_var_id >= variable_count ||
            graph->local_by_graph_var[ref->graph_var_id] != local ||
            ref->var_edge_begin != expected_var_begin ||
            ref->var_edge_count > edge_count - expected_var_begin ||
            ref->var_edge_count == 0 || ref->reserved[0] != 0 ||
            ref->reserved[1] != 0 || ref->reserved[2] != 0) return false;
        variable = &g_array_index(source->vars, OspreyVar,
                                  ref->graph_var_id);
        if (variable->id != ref->graph_var_id ||
            variable->hard_false > 1 || variable->region_limit_hit > 1 ||
            variable->belief_valid > 1 ||
            !exact_payload_valid(variable->kind, &variable->payload) ||
            ref->base_seed_valid > 1) {
            return false;
        }
        if (ref->base_seed_valid) {
            if (!isfinite(ref->base_seed[0]) ||
                !isfinite(ref->base_seed[1]) ||
                ref->base_seed[0] < 0.0 || ref->base_seed[1] < 0.0 ||
                ref->base_seed[0] > 1.0 || ref->base_seed[1] > 1.0 ||
                ref->base_seed[0] != 1.0 - ref->base_seed[1]) return false;
            if (graph->message_state == OSPREY_BP_MESSAGES_INITIAL &&
                (ref->base_seed_valid != variable->belief_valid ||
                 !isfinite(variable->belief) || variable->belief < 0.0 ||
                 variable->belief > 1.0 ||
                 ref->base_seed[1] != variable->belief ||
                 ref->base_seed[0] != 1.0 - variable->belief)) {
                return false;
            }
        } else if (!isnan(ref->base_seed[0]) ||
                   !isnan(ref->base_seed[1])) {
            return false;
        } else if (graph->message_state == OSPREY_BP_MESSAGES_INITIAL &&
                   variable->belief_valid != 0) {
            return false;
        }
        if (local != 0) {
            const OspreyBpVarRef *previous = &g_array_index(
                graph->vars, OspreyBpVarRef, local - 1);
            const OspreyVar *previous_var = &g_array_index(
                source->vars, OspreyVar, previous->graph_var_id);
            int order = exact_cmp_u64(previous_var->kind, variable->kind);
            if (order == 0) {
                order = osprey_var_payload_compare(
                    previous_var->kind, &previous_var->payload,
                    &variable->payload);
            }
            if (order >= 0) return false;
        }
        expected_var_begin += ref->var_edge_count;
    }
    if (expected_var_begin != edge_count) return false;
    for (uint32_t graph_id = 0; graph_id < variable_count; graph_id++) {
        uint32_t local = graph->local_by_graph_var[graph_id];
        if (local >= variable_count ||
            g_array_index(graph->vars, OspreyBpVarRef, local).graph_var_id !=
                graph_id) return false;
    }

    for (uint32_t local_factor = 0; local_factor < factor_count;
         local_factor++) {
        const OspreyBpFactorRef *ref = &g_array_index(
            graph->factors, OspreyBpFactorRef, local_factor);
        OspreyFactor *factor;

        if (ref->graph_factor_id >= factor_count ||
            graph->local_by_graph_factor[ref->graph_factor_id] !=
                local_factor || ref->factor_edge_begin != expected_begin ||
            expected_begin > edge_count ||
            ref->factor_edge_count > edge_count - expected_begin) {
            return false;
        }
        factor = g_array_index(source->factors, OspreyFactor *,
                               ref->graph_factor_id);
        if (!bp_source_factor_valid(factor, source) ||
            factor->num_vars != ref->factor_edge_count) return false;
        if (local_factor != 0) {
            const OspreyBpFactorRef *previous_ref = &g_array_index(
                graph->factors, OspreyBpFactorRef, local_factor - 1);
            const OspreyFactor *previous_factor = g_array_index(
                source->factors, OspreyFactor *,
                previous_ref->graph_factor_id);
            OspreyFactorKey previous_key = bp_factor_semantic_key(
                previous_factor, graph->local_by_graph_var);
            OspreyFactorKey key = bp_factor_semantic_key(
                factor, graph->local_by_graph_var);
            if (bp_factor_key_compare(&previous_key, &key) >= 0) {
                return false;
            }
        }
        for (uint32_t position = 0; position < factor->num_vars; position++) {
            uint32_t edge_id = ref->factor_edge_begin + position;
            const OspreyBpEdge *edge;
            const OspreyVar *variable;
            OspreyBpEdgeKey expected_key;

            if (edge_id >= edge_count) return false;
            edge = &g_array_index(graph->edges, OspreyBpEdge, edge_id);
            if (edge->id != edge_id || edge->local_factor != local_factor ||
                edge->factor_position != position ||
                edge->graph_factor_id != ref->graph_factor_id ||
                edge->graph_var_id >= variable_count ||
                edge->local_var !=
                    graph->local_by_graph_var[edge->graph_var_id] ||
                factor->var_ids[position] != edge->graph_var_id ||
                edge->key.reserved != 0 ||
                edge->key.factor.reserved != 0 ||
                edge->key.factor.reserved2 != 0) return false;
            variable = &g_array_index(source->vars, OspreyVar,
                                      edge->graph_var_id);
            memset(&expected_key, 0, sizeof(expected_key));
            expected_key.factor = bp_factor_semantic_key(
                factor, graph->local_by_graph_var);
            expected_key.variable = osprey_var_key(variable->kind,
                                                   &variable->payload);
            expected_key.factor_position = position;
            if (bp_edge_key_compare(&edge->key, &expected_key) != 0) {
                return false;
            }
        }
        expected_begin += ref->factor_edge_count;
    }
    if (expected_begin != edge_count) return false;
    for (uint32_t graph_id = 0; graph_id < factor_count; graph_id++) {
        uint32_t local = graph->local_by_graph_factor[graph_id];
        if (local >= factor_count ||
            g_array_index(graph->factors, OspreyBpFactorRef, local)
                .graph_factor_id != graph_id) return false;
    }

    for (uint32_t local_var = 0; local_var < variable_count; local_var++) {
        const OspreyBpVarRef *ref = &g_array_index(
            graph->vars, OspreyBpVarRef, local_var);
        const OspreyBpEdge *previous = NULL;

        for (uint32_t i = 0; i < ref->var_edge_count; i++) {
            uint32_t edge_id = g_array_index(
                graph->var_edges, uint32_t, ref->var_edge_begin + i);
            const OspreyBpEdge *edge;
            if (edge_id >= edge_count) return false;
            edge = &g_array_index(graph->edges, OspreyBpEdge, edge_id);
            if (edge->local_var != local_var ||
                (previous != NULL &&
                 bp_edge_key_compare(&previous->key, &edge->key) >= 0)) {
                return false;
            }
            previous = edge;
        }
    }
    *edge_count_out = edge_count;
    return true;
}

static bool bp_message_buffers_disjoint(const OspreyBpMessages *messages,
                                        uint64_t value_count)
{
    const double *buffers[4];
    uintptr_t begins[4];
    uintptr_t ends[4];
    size_t bytes;

    if (messages == NULL || value_count == 0 ||
        value_count > SIZE_MAX / sizeof(double)) return false;
    bytes = (size_t)value_count * sizeof(double);
    buffers[0] = messages->vf_current;
    buffers[1] = messages->vf_next;
    buffers[2] = messages->fv_current;
    buffers[3] = messages->fv_next;
    for (size_t i = 0; i < G_N_ELEMENTS(buffers); i++) {
        begins[i] = (uintptr_t)buffers[i];
        if (begins[i] > UINTPTR_MAX - bytes) return false;
        ends[i] = begins[i] + bytes;
    }
    for (size_t i = 0; i < G_N_ELEMENTS(buffers); i++) {
        for (size_t j = i + 1; j < G_N_ELEMENTS(buffers); j++) {
            if (begins[i] < ends[j] && begins[j] < ends[i]) return false;
        }
    }
    return true;
}

static bool bp_round_messages_valid(const OspreyBpGraph *graph,
                                    OspreyBpMessages *messages,
                                    uint32_t edge_count)
{
    uint64_t value_count;

    if (graph == NULL || messages == NULL || messages->vf_current == NULL ||
        messages->vf_next == NULL || messages->fv_current == NULL ||
        messages->fv_next == NULL ||
        !bp_u64_mul(edge_count, 2u, &value_count)) return false;
    if (messages->value_count != value_count ||
        graph->message_values != value_count ||
        !bp_message_buffers_disjoint(messages, value_count)) return false;
    for (uint64_t i = 0; i < value_count; i++) {
        uint64_t edge = i / 2u;
        if ((i & 1u) == 0 && !bp_log_pair_valid(
                messages->vf_current[(size_t)edge * 2u],
                messages->vf_current[(size_t)edge * 2u + 1u])) return false;
        if ((i & 1u) == 0 && !bp_log_pair_valid(
                messages->fv_current[(size_t)edge * 2u],
                messages->fv_current[(size_t)edge * 2u + 1u])) return false;
    }
    return true;
}

static OspreyStatus bp_round_normalize_pair(double pair[2])
{
    double log_norm;

    if (pair == NULL) return OSPREY_INVALID_GRAPH;
    if (pair[0] == -INFINITY && pair[1] == -INFINITY) {
        return OSPREY_INVALID_MODEL;
    }
    if (!osprey_log_normalize(pair, 2, &log_norm) ||
        !bp_log_pair_valid(pair[0], pair[1])) {
        return OSPREY_INVALID_GRAPH;
    }
    return OSPREY_OK;
}

static OspreyStatus bp_compute_round_internal(
    const OspreyContext *ctx, const OspreyBpGraph *graph,
    OspreyBpMessages *messages, OspreyBpRoundStats *stats,
    bool damp_between_phases, double damping)
{
    uint32_t edge_count;
    uint32_t variable_messages = 0;
    uint32_t factor_messages = 0;
    OspreyStatus status;

    if (stats != NULL) memset(stats, 0, sizeof(*stats));
    if (!bp_round_graph_valid(ctx, graph, &edge_count) ||
        !bp_round_messages_valid(graph, messages, edge_count)) {
        return OSPREY_INVALID_GRAPH;
    }
    bp_round_clear_next(messages, messages->value_count);

    /* Variable -> factor: the destination edge is excluded from the
     * incoming factor-message product.  An empty product is neutral. */
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        const OspreyBpEdge *edge = &g_array_index(graph->edges,
                                                  OspreyBpEdge, edge_id);
        const OspreyBpVarRef *variable = &g_array_index(
            graph->vars, OspreyBpVarRef, edge->local_var);
        double output[2] = { 0.0, 0.0 };

        for (uint32_t i = 0; i < variable->var_edge_count; i++) {
            uint32_t incoming_id = g_array_index(
                graph->var_edges, uint32_t,
                variable->var_edge_begin + i);
            const double *incoming;
            if (incoming_id == edge_id) continue;
            if (incoming_id >= edge_count) {
                status = OSPREY_INVALID_GRAPH;
                goto fail;
            }
            incoming = &messages->fv_current[(size_t)incoming_id * 2u];
            if (!osprey_log_product_add(output[0], incoming[0], &output[0]) ||
                !osprey_log_product_add(output[1], incoming[1], &output[1])) {
                status = OSPREY_INVALID_GRAPH;
                goto fail;
            }
        }
        status = bp_round_normalize_pair(output);
        if (status != OSPREY_OK) goto fail;
        messages->vf_next[(size_t)edge_id * 2u] = output[0];
        messages->vf_next[(size_t)edge_id * 2u + 1u] = output[1];
        variable_messages++;
    }
    if (damp_between_phases) {
        for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
            size_t index = (size_t)edge_id * 2u;
            if (!osprey_bp_damp_pair(
                    &messages->vf_current[index], &messages->vf_next[index],
                    damping, &messages->vf_next[index])) {
                status = OSPREY_INVALID_GRAPH;
                goto fail;
            }
        }
    }

    /* Factor -> variable: enumerate every assignment of the other roles.
     * The factor's semantic order and head index are preserved by passing
     * the assignment directly to the shared factor evaluator. */
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        const OspreyBpEdge *edge = &g_array_index(graph->edges,
                                                  OspreyBpEdge, edge_id);
        const OspreyBpFactorRef *factor_ref = &g_array_index(
            graph->factors, OspreyBpFactorRef, edge->local_factor);
        const OspreyFactor *factor = g_array_index(
            ctx->graph->factors, OspreyFactor *,
            factor_ref->graph_factor_id);
        uint32_t arity = factor->num_vars;
        uint32_t alternatives = 1u << (arity - 1u);
        double output[2] = { -INFINITY, -INFINITY };

        for (uint32_t recipient_state = 0; recipient_state < 2;
             recipient_state++) {
            double raw = -INFINITY;
            for (uint32_t compact = 0; compact < alternatives; compact++) {
                uint8_t assignment[OSPREY_FACTOR_MAX_ARITY];
                uint32_t compact_bit = 0;
                double term;

                for (uint32_t position = 0; position < arity; position++) {
                    if (position == edge->factor_position) {
                        assignment[position] = recipient_state;
                    } else {
                        assignment[position] = (uint8_t)((compact >>
                                                          compact_bit++) & 1u);
                    }
                }
                if (!osprey_factor_log_weight(factor, assignment, &term)) {
                    status = OSPREY_INVALID_GRAPH;
                    goto fail;
                }
                for (uint32_t position = 0; position < arity; position++) {
                    uint32_t incoming_id;
                    const double *incoming;
                    if (position == edge->factor_position) continue;
                    incoming_id = factor_ref->factor_edge_begin + position;
                    if (incoming_id >= edge_count) {
                        status = OSPREY_INVALID_GRAPH;
                        goto fail;
                    }
                    incoming = &messages->vf_next[(size_t)incoming_id * 2u];
                    if (!osprey_log_product_add(
                            term, incoming[assignment[position]], &term)) {
                        status = OSPREY_INVALID_GRAPH;
                        goto fail;
                    }
                }
                if (!osprey_logaddexp(raw, term, &raw)) {
                    status = OSPREY_INVALID_GRAPH;
                    goto fail;
                }
            }
            output[recipient_state] = raw;
        }
        status = bp_round_normalize_pair(output);
        if (status != OSPREY_OK) goto fail;
        messages->fv_next[(size_t)edge_id * 2u] = output[0];
        messages->fv_next[(size_t)edge_id * 2u + 1u] = output[1];
        factor_messages++;
    }
    if (damp_between_phases) {
        for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
            size_t index = (size_t)edge_id * 2u;
            if (!osprey_bp_damp_pair(
                    &messages->fv_current[index], &messages->fv_next[index],
                    damping, &messages->fv_next[index])) {
                status = OSPREY_INVALID_GRAPH;
                goto fail;
            }
        }
    }
    if (stats != NULL) {
        stats->variable_messages = variable_messages;
        stats->factor_messages = factor_messages;
    }
    return OSPREY_OK;

fail:
    bp_round_clear_next(messages, messages->value_count);
    return status;
}

OspreyStatus osprey_bp_compute_round(const OspreyContext *ctx,
                                     const OspreyBpGraph *graph,
                                     OspreyBpMessages *messages,
                                     OspreyBpRoundStats *stats)
{
    return bp_compute_round_internal(ctx, graph, messages, stats, false, 0.0);
}

OspreyStatus osprey_bp_compute_round_damped(
    const OspreyContext *ctx, const OspreyBpGraph *graph,
    OspreyBpMessages *messages, OspreyBpRoundStats *stats,
    double coefficient)
{
    return bp_compute_round_internal(ctx, graph, messages, stats, true,
                                     coefficient);
}

/* ------------------------------------------------------------------ */
/* Stage 5.3: fixed-graph damping, convergence, and publication        */
/* ------------------------------------------------------------------ */

static bool bp_probability_from_log_pair(const double pair[2], double *out)
{
    double probability;

    if (pair == NULL || out == NULL || !bp_log_pair_valid(pair[0], pair[1])) {
        return false;
    }
    if (pair[1] == -INFINITY) {
        *out = 0.0;
        return true;
    }
    if (pair[0] == -INFINITY) {
        *out = 1.0;
        return true;
    }
    probability = exp(pair[1]);
    /* A finite log weight must not become an exact support zero or one while
     * converting the normalized pair to the public binary marginal. */
    if (!isfinite(probability) || !(probability > 0.0) ||
        !(probability < 1.0)) return false;
    *out = probability;
    return true;
}

bool osprey_bp_damp_pair(const double current[2], const double raw[2],
                         double coefficient, double out[2])
{
    double current_pair[2];
    double raw_pair[2];
    double log_current_weight;
    double log_raw_weight;
    double mixed[2];

    if (current == NULL || raw == NULL || out == NULL ||
        !isfinite(coefficient) || coefficient < 0.0 || coefficient > 1.0) {
        return false;
    }
    current_pair[0] = current[0];
    current_pair[1] = current[1];
    raw_pair[0] = raw[0];
    raw_pair[1] = raw[1];
    if (!bp_log_pair_valid(current_pair[0], current_pair[1]) ||
        !bp_log_pair_valid(raw_pair[0], raw_pair[1])) return false;
    if (coefficient == 1.0) {
        out[0] = current_pair[0];
        out[1] = current_pair[1];
        return true;
    }
    if (coefficient == 0.0) {
        out[0] = raw_pair[0];
        out[1] = raw_pair[1];
        return true;
    }
    log_current_weight = log(coefficient);
    log_raw_weight = log1p(-coefficient);
    if (!isfinite(log_current_weight) || !isfinite(log_raw_weight)) {
        return false;
    }
    for (unsigned state = 0; state < 2; state++) {
        double current_term;
        double raw_term;
        if (!osprey_log_product_add(log_current_weight,
                                    current_pair[state], &current_term) ||
            !osprey_log_product_add(log_raw_weight, raw_pair[state],
                                    &raw_term) ||
            !osprey_logaddexp(current_term, raw_term, &mixed[state])) {
            return false;
        }
    }
    return bp_round_normalize_pair(mixed) == OSPREY_OK &&
           (out[0] = mixed[0], out[1] = mixed[1], true);
}

static OspreyStatus bp_belief_from_next(const OspreyBpGraph *graph,
                                         uint32_t local, double *out)
{
    const OspreyBpVarRef *variable;
    double pair[2] = { 0.0, 0.0 };
    double log_norm;

    if (graph == NULL || out == NULL || graph->vars == NULL ||
        graph->var_edges == NULL || local >= graph->vars->len) {
        return OSPREY_INVALID_GRAPH;
    }
    variable = &g_array_index(graph->vars, OspreyBpVarRef, local);
    if (variable->var_edge_count == 0 ||
        variable->var_edge_begin > graph->edges->len ||
        variable->var_edge_count > graph->edges->len -
                                   variable->var_edge_begin) {
        return OSPREY_INVALID_GRAPH;
    }
    for (uint32_t i = 0; i < variable->var_edge_count; i++) {
        uint32_t edge_id = g_array_index(graph->var_edges, uint32_t,
                                         variable->var_edge_begin + i);
        const double *incoming;
        if (edge_id >= graph->edges->len) return OSPREY_INVALID_GRAPH;
        incoming = &graph->msg_fv_next[(size_t)edge_id * 2u];
        if (!osprey_log_product_add(pair[0], incoming[0], &pair[0]) ||
            !osprey_log_product_add(pair[1], incoming[1], &pair[1])) {
            return OSPREY_INVALID_GRAPH;
        }
    }
    if (pair[0] == -INFINITY && pair[1] == -INFINITY) {
        return OSPREY_INVALID_MODEL;
    }
    if (!osprey_log_normalize(pair, 2, &log_norm) ||
        !isfinite(log_norm)) {
        return OSPREY_INVALID_GRAPH;
    }
    if (!bp_probability_from_log_pair(pair, out)) {
        return OSPREY_INVALID_GRAPH;
    }
    return OSPREY_OK;
}

static OspreyStatus bp_compute_next_beliefs(
    const OspreyBpGraph *graph, double *beliefs, double *max_delta_out,
    uint32_t *unstable_component_out, bool *all_stable_out)
{
    double max_delta = 0.0;
    uint32_t unstable_component = UINT32_MAX;
    bool all_stable = true;

    if (graph == NULL || beliefs == NULL || max_delta_out == NULL ||
        unstable_component_out == NULL || all_stable_out == NULL ||
        graph->components == NULL || graph->beliefs == NULL) {
        return OSPREY_INVALID_GRAPH;
    }
    for (guint component_id = 0; component_id < graph->components->len;
         component_id++) {
        const OspreyBpComponent *component = g_ptr_array_index(
            graph->components, component_id);
        double component_delta = 0.0;

        if (component == NULL || component->local_vars == NULL ||
            component->local_vars->len == 0) return OSPREY_INVALID_GRAPH;
        for (guint i = 0; i < component->local_vars->len; i++) {
            uint32_t local = g_array_index(component->local_vars, uint32_t, i);
            double delta;
            OspreyStatus status;

            if (local >= graph->vars->len) return OSPREY_INVALID_GRAPH;
            status = bp_belief_from_next(graph, local, &beliefs[local]);
            if (status != OSPREY_OK) return status;
            if (!isfinite(graph->beliefs[local]) ||
                !isfinite(beliefs[local])) return OSPREY_INVALID_GRAPH;
            delta = fabs(beliefs[local] - graph->beliefs[local]);
            if (!isfinite(delta)) return OSPREY_INVALID_GRAPH;
            if (delta > component_delta) component_delta = delta;
            if (delta > max_delta) max_delta = delta;
        }
        if (!(component_delta < OSPREY_BP_TOL)) {
            all_stable = false;
            if (unstable_component == UINT32_MAX) {
                unstable_component = component_id;
            }
        }
    }
    *max_delta_out = max_delta;
    *unstable_component_out = unstable_component;
    *all_stable_out = all_stable;
    return OSPREY_OK;
}

/* Exact zero-weight factors form Horn clauses under the accepted generic
 * potentials: p=1 implications force their head after every antecedent is
 * true; p=0 implications, p=0 priors, and hard-false factors forbid all of
 * their variables being true.  Forward chaining over the least Horn model
 * decides support in O(V+E+F), unlike assignment enumeration over a complete
 * component. */
static OspreyStatus bp_graph_support_check(const OspreyContext *ctx,
                                           OspreyBpGraph *graph)
{
    uint32_t variable_count;
    uint32_t factor_count;
    uint64_t scratch_bytes_u64;
    size_t scratch_bytes;
    size_t queue_offset;
    size_t required;
    uint8_t *truth;
    uint8_t *remaining;
    uint32_t *queue;
    uint32_t queue_head = 0;
    uint32_t queue_tail = 0;
    OspreyStatus status = OSPREY_OK;

    if (ctx == NULL || graph == NULL || ctx->graph == NULL ||
        graph->vars == NULL || graph->factors == NULL ||
        graph->edges == NULL || graph->var_edges == NULL ||
        graph->scratch_message == NULL ||
        graph->vars->len == 0 || graph->vars->len > UINT32_MAX ||
        graph->factors->len == 0 || graph->factors->len > UINT32_MAX ||
        graph->message_values > SIZE_MAX / sizeof(double)) {
        return OSPREY_INVALID_GRAPH;
    }
    variable_count = graph->vars->len;
    factor_count = graph->factors->len;
    scratch_bytes_u64 = graph->message_values * sizeof(double);
    scratch_bytes = (size_t)scratch_bytes_u64;
    if ((size_t)variable_count > SIZE_MAX - (size_t)factor_count) {
        return OSPREY_INVALID_GRAPH;
    }
    queue_offset = (size_t)variable_count + (size_t)factor_count;
    if (queue_offset > SIZE_MAX - (sizeof(uint32_t) - 1u)) {
        return OSPREY_INVALID_GRAPH;
    }
    queue_offset = (queue_offset + sizeof(uint32_t) - 1u) &
                   ~(sizeof(uint32_t) - 1u);
    if ((size_t)variable_count >
        (SIZE_MAX - queue_offset) / sizeof(uint32_t)) {
        return OSPREY_INVALID_GRAPH;
    }
    required = queue_offset + (size_t)variable_count * sizeof(uint32_t);
    if (required > scratch_bytes) return OSPREY_INVALID_GRAPH;

    truth = (uint8_t *)graph->scratch_message;
    remaining = truth + variable_count;
    queue = (uint32_t *)(truth + queue_offset);
    memset(truth, 0, required);

    for (uint32_t local_factor = 0; local_factor < factor_count;
         local_factor++) {
        const OspreyBpFactorRef *ref = &g_array_index(
            graph->factors, OspreyBpFactorRef, local_factor);
        const OspreyFactor *factor;

        if (ref->graph_factor_id >= ctx->graph->factors->len) {
            status = OSPREY_INVALID_GRAPH;
            goto out;
        }
        factor = g_array_index(ctx->graph->factors, OspreyFactor *,
                               ref->graph_factor_id);
        if (factor == NULL || factor->num_vars == 0 ||
            factor->num_vars > OSPREY_FACTOR_MAX_ARITY ||
            factor->num_vars != ref->factor_edge_count ||
            ref->factor_edge_begin > graph->edges->len ||
            ref->factor_edge_count > graph->edges->len -
                                     ref->factor_edge_begin) {
            status = OSPREY_INVALID_GRAPH;
            goto out;
        }
        if (factor->potential_kind == OSPREY_POTENTIAL_PRIOR &&
            factor->p == 1.0) {
            const OspreyBpEdge *edge = &g_array_index(
                graph->edges, OspreyBpEdge, ref->factor_edge_begin);
            if (edge->local_var >= variable_count) {
                status = OSPREY_INVALID_GRAPH;
                goto out;
            }
            if (!truth[edge->local_var]) {
                if (queue_tail >= variable_count) {
                    status = OSPREY_INVALID_GRAPH;
                    goto out;
                }
                truth[edge->local_var] = 1;
                queue[queue_tail++] = edge->local_var;
            }
        } else if (factor->potential_kind == OSPREY_POTENTIAL_IMPLICATION &&
                   factor->p == 1.0) {
            remaining[local_factor] = factor->num_vars - 1u;
        } else if ((factor->potential_kind == OSPREY_POTENTIAL_PRIOR &&
                    factor->p == 0.0) ||
                   (factor->potential_kind == OSPREY_POTENTIAL_IMPLICATION &&
                    factor->p == 0.0) ||
                   factor->potential_kind == OSPREY_POTENTIAL_HARD_FALSE) {
            remaining[local_factor] = factor->num_vars;
        }
    }

    while (queue_head < queue_tail) {
        uint32_t local_var = queue[queue_head++];
        const OspreyBpVarRef *variable;

        if (local_var >= variable_count) {
            status = OSPREY_INVALID_GRAPH;
            goto out;
        }
        variable = &g_array_index(graph->vars, OspreyBpVarRef, local_var);
        if (variable->var_edge_begin > graph->var_edges->len ||
            variable->var_edge_count > graph->var_edges->len -
                                       variable->var_edge_begin) {
            status = OSPREY_INVALID_GRAPH;
            goto out;
        }
        for (uint32_t i = 0; i < variable->var_edge_count; i++) {
            uint32_t edge_id = g_array_index(
                graph->var_edges, uint32_t, variable->var_edge_begin + i);
            const OspreyBpEdge *edge;
            const OspreyBpFactorRef *ref;
            const OspreyFactor *factor;
            bool implication;
            bool forbidden;

            if (edge_id >= graph->edges->len) {
                status = OSPREY_INVALID_GRAPH;
                goto out;
            }
            edge = &g_array_index(graph->edges, OspreyBpEdge, edge_id);
            if (edge->local_var != local_var ||
                edge->local_factor >= factor_count) {
                status = OSPREY_INVALID_GRAPH;
                goto out;
            }
            ref = &g_array_index(graph->factors, OspreyBpFactorRef,
                                 edge->local_factor);
            if (ref->graph_factor_id >= ctx->graph->factors->len) {
                status = OSPREY_INVALID_GRAPH;
                goto out;
            }
            factor = g_array_index(ctx->graph->factors, OspreyFactor *,
                                   ref->graph_factor_id);
            implication = factor->potential_kind ==
                              OSPREY_POTENTIAL_IMPLICATION &&
                          factor->p == 1.0;
            forbidden = ((factor->potential_kind == OSPREY_POTENTIAL_PRIOR ||
                          factor->potential_kind ==
                              OSPREY_POTENTIAL_IMPLICATION) &&
                         factor->p == 0.0) ||
                        factor->potential_kind ==
                            OSPREY_POTENTIAL_HARD_FALSE;
            if (implication && edge->factor_position != factor->head_idx) {
                if (remaining[edge->local_factor] == 0) {
                    status = OSPREY_INVALID_GRAPH;
                    goto out;
                }
                remaining[edge->local_factor]--;
                if (remaining[edge->local_factor] == 0) {
                    uint32_t head_edge_id = ref->factor_edge_begin +
                                            factor->head_idx;
                    const OspreyBpEdge *head_edge;
                    if (head_edge_id >= graph->edges->len) {
                        status = OSPREY_INVALID_GRAPH;
                        goto out;
                    }
                    head_edge = &g_array_index(graph->edges, OspreyBpEdge,
                                               head_edge_id);
                    if (head_edge->local_var >= variable_count) {
                        status = OSPREY_INVALID_GRAPH;
                        goto out;
                    }
                    if (!truth[head_edge->local_var]) {
                        if (queue_tail >= variable_count) {
                            status = OSPREY_INVALID_GRAPH;
                            goto out;
                        }
                        truth[head_edge->local_var] = 1;
                        queue[queue_tail++] = head_edge->local_var;
                    }
                }
            } else if (forbidden) {
                if (remaining[edge->local_factor] == 0) {
                    status = OSPREY_INVALID_GRAPH;
                    goto out;
                }
                remaining[edge->local_factor]--;
                if (remaining[edge->local_factor] == 0) {
                    status = OSPREY_INVALID_MODEL;
                    goto out;
                }
            }
        }
    }

out:
    for (uint64_t i = 0; i < graph->message_values; i++) {
        graph->scratch_message[i] = NAN;
    }
    return status;
}

static bool bp_result_workspace_bytes(const OspreyBpGraph *graph,
                                      uint64_t *out)
{
    uint64_t total;
    uint64_t saved_message_values;
    uint64_t saved_belief_values;

    if (graph == NULL || out == NULL || graph->vars == NULL ||
        graph->vars->len == 0) return false;
    if (!bp_u64_mul(graph->message_values, 2u, &saved_message_values) ||
        !bp_u64_mul(graph->vars->len, 2u, &saved_belief_values)) return false;
    total = graph->workspace_bytes;
    if (!bp_u64_add(&total, sizeof(OspreyBpResult)) ||
        !bp_u64_add(&total, sizeof(GArray)) ||
        !bp_workspace_add(&total, graph->vars->len, sizeof(double)) ||
        !bp_workspace_add(&total, saved_message_values, sizeof(double)) ||
        !bp_workspace_add(&total, saved_belief_values, sizeof(double))) {
        return false;
    }
    *out = total;
    return true;
}

static OspreyBpResult *bp_result_new(const OspreyBpGraph *graph)
{
    OspreyBpResult *result;

    if (graph == NULL || graph->vars == NULL ||
        graph->vars->len > G_MAXUINT) return NULL;
    result = bp_try_alloc0(sizeof(*result));
    if (result == NULL) return NULL;
    result->status = OSPREY_INVALID_GRAPH;
    result->nonconverged_component = UINT32_MAX;
    result->final_max_delta = NAN;
    result->best_max_delta = INFINITY;
    result->owner = graph;
    result->beliefs = bp_array_new(sizeof(double), graph->vars->len);
    if (result->beliefs == NULL) {
        g_free(result);
        return NULL;
    }
    g_array_set_size(result->beliefs, graph->vars->len);
    for (guint i = 0; i < result->beliefs->len; i++) {
        g_array_index(result->beliefs, double, i) = NAN;
    }
    return result;
}

void osprey_bp_result_free(OspreyBpResult *result)
{
    if (result == NULL) return;
    if (result->beliefs != NULL) g_array_free(result->beliefs, TRUE);
    g_free(result);
}

static void bp_restore_saved_state(
    OspreyBpGraph *graph, double *saved_vf_current_buffer,
    double *saved_vf_next_buffer, double *saved_fv_current_buffer,
    double *saved_fv_next_buffer, const double *saved_vf,
    const double *saved_fv, const double *saved_beliefs,
    OspreyBpMessageState message_state)
{
    if (graph == NULL || saved_vf_current_buffer == NULL ||
        saved_vf_next_buffer == NULL || saved_fv_current_buffer == NULL ||
        saved_fv_next_buffer == NULL || saved_vf == NULL || saved_fv == NULL ||
        saved_beliefs == NULL) return;
    graph->msg_vf_current = saved_vf_current_buffer;
    graph->msg_vf_next = saved_vf_next_buffer;
    graph->msg_fv_current = saved_fv_current_buffer;
    graph->msg_fv_next = saved_fv_next_buffer;
    memcpy(graph->msg_vf_current, saved_vf,
           (size_t)graph->message_values * sizeof(double));
    memcpy(graph->msg_fv_current, saved_fv,
           (size_t)graph->message_values * sizeof(double));
    memcpy(graph->beliefs, saved_beliefs,
           (size_t)graph->vars->len * 2u * sizeof(double));
    graph->message_state = message_state;
    for (uint64_t i = 0; i < graph->message_values; i++) {
        graph->msg_vf_next[i] = NAN;
        graph->msg_fv_next[i] = NAN;
    }
}

static void bp_swap_round_buffers(OspreyBpGraph *graph)
{
    double *swap;

    swap = graph->msg_vf_current;
    graph->msg_vf_current = graph->msg_vf_next;
    graph->msg_vf_next = swap;
    swap = graph->msg_fv_current;
    graph->msg_fv_current = graph->msg_fv_next;
    graph->msg_fv_next = swap;
    for (uint64_t i = 0; i < graph->message_values; i++) {
        graph->msg_vf_next[i] = NAN;
        graph->msg_fv_next[i] = NAN;
    }
}

static OspreyStatus bp_fixed_failure(OspreyStatus status, const char *reason)
{
    log_msg("[osprey] [infer] [bp] [stage 5.3] [reject] [reason %s]\n",
            reason == NULL ? "unknown" : reason);
    return status;
}

static void bp_log_fixed_result(const OspreyBpGraph *graph,
                                const OspreyBpResult *result,
                                uint64_t workspace)
{
    uint64_t delta_bits;

    memcpy(&delta_bits, &result->final_max_delta, sizeof(delta_bits));
    log_msg("[osprey] [infer] [bp] [version 0] [components %u] "
            "[vars %u] [factors %u] [edges %u] [iters %u] "
            "[converged %u] [max-delta %016llx] [stable %u] "
            "[workspace %llu]\n",
            graph->components->len, graph->vars->len, graph->factors->len,
            graph->edges->len, result->iterations,
            result->status == OSPREY_OK ? 1 : 0,
            (unsigned long long)delta_bits, result->stable_rounds,
            (unsigned long long)workspace);
}

OspreyStatus osprey_bp_solve_fixed(OspreyContext *ctx,
                                   OspreyBpGraph *graph,
                                   OspreyBpResult **out)
{
    OspreyBpMessages messages;
    OspreyBpResult *result = NULL;
    uint32_t edge_count;
    uint32_t variable_count;
    uint32_t stable_rounds = 0;
    uint32_t last_unstable_component = UINT32_MAX;
    uint64_t workspace_required;
    uint64_t belief_bytes_u64;
    uint64_t message_bytes_u64;
    uint64_t saved_belief_values;
    uint64_t saved_belief_bytes_u64;
    size_t belief_bytes;
    size_t message_bytes;
    size_t saved_belief_bytes;
    double *saved_vf_current_buffer = NULL;
    double *saved_vf_next_buffer = NULL;
    double *saved_fv_current_buffer = NULL;
    double *saved_fv_next_buffer = NULL;
    double *saved_vf = NULL;
    double *saved_fv = NULL;
    double *saved_beliefs = NULL;
    OspreyBpMessageState saved_message_state;
    OspreyStatus status;
    bool initial_state;
    bool policy_converged = false;

    if (out != NULL) *out = NULL;
    if (ctx == NULL || graph == NULL || out == NULL ||
        !ctx->config.enabled) {
        return ctx != NULL && !ctx->config.enabled
            ? OSPREY_DISABLED : OSPREY_INVALID_GRAPH;
    }
    if (!osprey_bp_graph_validate(ctx, graph) ||
        !bp_round_graph_valid(ctx, graph, &edge_count) ||
        !bp_round_messages_valid(graph, &(OspreyBpMessages){
            graph->msg_vf_current, graph->msg_vf_next,
            graph->msg_fv_current, graph->msg_fv_next, graph->message_values
        }, edge_count)) {
        return bp_fixed_failure(OSPREY_INVALID_GRAPH, "invalid fixed graph");
    }
    if (!bp_result_workspace_bytes(graph, &workspace_required)) {
        return bp_fixed_failure(OSPREY_LIMIT_EXCEEDED,
                                "fixed result workspace overflow");
    }
    if (workspace_required > graph->workspace_limit) {
        return bp_fixed_failure(OSPREY_LIMIT_EXCEEDED,
                                "fixed result workspace limit");
    }
    result = bp_result_new(graph);
    if (result == NULL) {
        return bp_fixed_failure(OSPREY_INVALID_GRAPH,
                                "allocation fixed result");
    }
    variable_count = graph->vars->len;
    if (!bp_bytes_for(variable_count, sizeof(double), &belief_bytes_u64) ||
        belief_bytes_u64 > SIZE_MAX) {
        osprey_bp_result_free(result);
        return bp_fixed_failure(OSPREY_LIMIT_EXCEEDED,
                                "fixed belief size overflow");
    }
    belief_bytes = (size_t)belief_bytes_u64;
    if (!bp_bytes_for(graph->message_values, sizeof(double),
                      &message_bytes_u64) ||
        message_bytes_u64 > SIZE_MAX ||
        !bp_u64_mul((uint64_t)variable_count, 2u,
                    &saved_belief_values) ||
        !bp_bytes_for(saved_belief_values, sizeof(double),
                      &saved_belief_bytes_u64) ||
        saved_belief_bytes_u64 > SIZE_MAX) {
        osprey_bp_result_free(result);
        return bp_fixed_failure(OSPREY_LIMIT_EXCEEDED,
                                "fixed snapshot size overflow");
    }
    message_bytes = (size_t)message_bytes_u64;
    saved_belief_bytes = (size_t)saved_belief_bytes_u64;
    saved_vf = bp_try_alloc(message_bytes);
    saved_fv = bp_try_alloc(message_bytes);
    saved_beliefs = bp_try_alloc(saved_belief_bytes);
    if (saved_vf == NULL || saved_fv == NULL || saved_beliefs == NULL) {
        g_free(saved_vf);
        g_free(saved_fv);
        g_free(saved_beliefs);
        osprey_bp_result_free(result);
        return bp_fixed_failure(OSPREY_INVALID_GRAPH,
                                "allocation fixed snapshots");
    }
    saved_vf_current_buffer = graph->msg_vf_current;
    saved_vf_next_buffer = graph->msg_vf_next;
    saved_fv_current_buffer = graph->msg_fv_current;
    saved_fv_next_buffer = graph->msg_fv_next;
    memcpy(saved_vf, graph->msg_vf_current, message_bytes);
    memcpy(saved_fv, graph->msg_fv_current, message_bytes);
    memcpy(saved_beliefs, graph->beliefs, saved_belief_bytes);
    saved_message_state = graph->message_state;
    initial_state = saved_message_state == OSPREY_BP_MESSAGES_INITIAL;
    if (initial_state) {
        for (uint32_t local = 0; local < variable_count; local++) {
            const OspreyBpVarRef *variable = &g_array_index(
                graph->vars, OspreyBpVarRef, local);
            graph->beliefs[local] = variable->base_seed_valid
                ? variable->base_seed[1] : 0.5;
            graph->beliefs[variable_count + local] = NAN;
        }
    }
    status = bp_graph_support_check(ctx, graph);
    if (status != OSPREY_OK) goto solve_fail;
    for (uint32_t iteration = 1; iteration <= OSPREY_BP_MAX_ITERS;
         iteration++) {
        double max_delta;
        messages.vf_current = graph->msg_vf_current;
        messages.vf_next = graph->msg_vf_next;
        messages.fv_current = graph->msg_fv_current;
        messages.fv_next = graph->msg_fv_next;
        messages.value_count = graph->message_values;
        uint32_t unstable_component;
        bool all_stable;

        status = osprey_bp_compute_round_damped(
            ctx, graph, &messages, NULL, OSPREY_BP_DAMPING);
        if (status != OSPREY_OK) goto solve_fail;
        status = bp_compute_next_beliefs(
            graph, (double *)result->beliefs->data, &max_delta,
            &unstable_component, &all_stable);
        if (status != OSPREY_OK) goto solve_fail;
        result->iterations = iteration;
        result->final_max_delta = max_delta;
        if (max_delta < result->best_max_delta) {
            result->best_max_delta = max_delta;
            result->best_iteration = iteration;
            memcpy(&graph->beliefs[variable_count], result->beliefs->data,
                   belief_bytes);
        }
        memcpy(graph->beliefs, result->beliefs->data, belief_bytes);
        if (unstable_component != UINT32_MAX) {
            last_unstable_component = unstable_component;
        }
        if (policy_converged) {
            if (!all_stable) {
                policy_converged = false;
                stable_rounds = 0;
            }
        } else {
            if (all_stable) {
                stable_rounds++;
            } else {
                stable_rounds = 0;
            }
            if (all_stable && stable_rounds >= OSPREY_BP_CONVERGED_ROUNDS) {
                policy_converged = true;
            }
        }
        result->stable_rounds = stable_rounds;
        bp_swap_round_buffers(graph);
        graph->message_state = OSPREY_BP_MESSAGES_ITERATED;
        if (policy_converged) {
            result->status = OSPREY_OK;
            result->nonconverged_component = UINT32_MAX;
            bp_log_fixed_result(graph, result, workspace_required);
            g_free(saved_vf);
            g_free(saved_fv);
            g_free(saved_beliefs);
            *out = result;
            return OSPREY_OK;
        }
    }
    result->status = OSPREY_NON_CONVERGED;
    result->nonconverged_component = last_unstable_component;
    if (isfinite(result->best_max_delta)) {
        memcpy(result->beliefs->data, &graph->beliefs[variable_count],
               belief_bytes);
    }
    bp_restore_saved_state(
        graph, saved_vf_current_buffer, saved_vf_next_buffer,
        saved_fv_current_buffer, saved_fv_next_buffer, saved_vf, saved_fv,
        saved_beliefs, saved_message_state);
    bp_log_fixed_result(graph, result, workspace_required);
    g_free(saved_vf);
    g_free(saved_fv);
    g_free(saved_beliefs);
    *out = result;
    return OSPREY_NON_CONVERGED;

solve_fail:
    result->status = status;
    result->nonconverged_component = last_unstable_component;
    for (guint i = 0; i < result->beliefs->len; i++) {
        g_array_index(result->beliefs, double, i) = NAN;
    }
    bp_restore_saved_state(
        graph, saved_vf_current_buffer, saved_vf_next_buffer,
        saved_fv_current_buffer, saved_fv_next_buffer, saved_vf, saved_fv,
        saved_beliefs, saved_message_state);
    g_free(saved_vf);
    g_free(saved_fv);
    g_free(saved_beliefs);
    bp_log_fixed_result(graph, result, workspace_required);
    *out = result;
    return bp_fixed_failure(status,
                            status == OSPREY_INVALID_MODEL
                                ? "impossible fixed graph"
                                : "fixed graph round failed");
}

OspreyStatus osprey_bp_commit_result(OspreyContext *ctx,
                                     const OspreyBpGraph *graph,
                                     const OspreyBpResult *result)
{
    if (ctx == NULL || graph == NULL || result == NULL ||
        graph->vars == NULL || result->owner != graph ||
        result->status != OSPREY_OK || result->beliefs == NULL ||
        result->beliefs->data == NULL ||
        result->beliefs->len != graph->vars->len ||
        g_array_get_element_size(result->beliefs) != sizeof(double) ||
        !osprey_bp_graph_validate(ctx, graph)) {
        return result != NULL && result->status != OSPREY_OK
            ? result->status : OSPREY_INVALID_GRAPH;
    }
    for (guint local = 0; local < result->beliefs->len; local++) {
        double belief = g_array_index(result->beliefs, double, local);
        if (!isfinite(belief) || belief < 0.0 || belief > 1.0) {
            return OSPREY_INVALID_GRAPH;
        }
    }
    for (guint local = 0; local < graph->vars->len; local++) {
        const OspreyBpVarRef *ref = &g_array_index(graph->vars,
                                                   OspreyBpVarRef, local);
        OspreyVar *variable = &g_array_index(ctx->graph->vars, OspreyVar,
                                              ref->graph_var_id);
        variable->belief = g_array_index(result->beliefs, double, local);
        variable->belief_valid = 1;
    }
    return OSPREY_OK;
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
