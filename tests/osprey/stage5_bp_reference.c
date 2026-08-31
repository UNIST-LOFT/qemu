#include "stage5_bp_reference.h"

#include <limits.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>

typedef struct RefVar {
    uint32_t graph_id;
    uint8_t kind;
    OspreyVarPayload payload;
    OspreyKey key;
} RefVar;

typedef struct RefFactor {
    uint32_t graph_id;
    OspreyFactorKey key;
} RefFactor;

typedef struct RefEdge {
    uint32_t id;
    uint32_t local_var;
    uint32_t local_factor;
    uint32_t factor_position;
    uint32_t graph_var_id;
    uint32_t graph_factor_id;
    OspreyFactorKey factor_key;
    OspreyKey variable_key;
} RefEdge;

static int ref_cmp_u64(uint64_t left, uint64_t right)
{
    return left < right ? -1 : left != right;
}

static int ref_cmp_i64(int64_t left, int64_t right)
{
    return left < right ? -1 : left != right;
}

static int ref_region_compare(const OspreyRegionId *left,
                              const OspreyRegionId *right)
{
    int result = ref_cmp_u64(left->kind, right->kind);
    if (result != 0) return result;
    result = ref_cmp_u64(left->code_image_id, right->code_image_id);
    if (result != 0) return result;
    return ref_cmp_u64(left->site_offset, right->site_offset);
}

static int ref_address_compare(const OspreyAddress *left,
                               const OspreyAddress *right)
{
    int result = ref_region_compare(&left->region, &right->region);
    return result != 0 ? result : ref_cmp_i64(left->offset, right->offset);
}

static int ref_chunk_compare(const OspreyChunk *left,
                             const OspreyChunk *right)
{
    int result = ref_address_compare(&left->address, &right->address);
    return result != 0 ? result : ref_cmp_u64(left->size, right->size);
}

static int ref_payload_compare(uint8_t kind, const OspreyVarPayload *left,
                               const OspreyVarPayload *right)
{
    int result;

    switch (kind) {
    case OSPREY_PRED_PRIMITIVE_VAR:
    case OSPREY_PRED_SCALAR:
        return ref_chunk_compare(&left->chunk, &right->chunk);
    case OSPREY_PRED_PRIMITIVE_ACCESS:
        result = ref_cmp_u64(left->prim_access.insn_pc,
                             right->prim_access.insn_pc);
        return result != 0 ? result : ref_chunk_compare(
            &left->prim_access.chunk, &right->prim_access.chunk);
    case OSPREY_PRED_UNFOLDABLE_HEAP:
    case OSPREY_PRED_FOLDABLE_HEAP:
        result = ref_region_compare(&left->heap_fold.region,
                                    &right->heap_fold.region);
        return result != 0 ? result : ref_cmp_u64(left->heap_fold.size,
                                                    right->heap_fold.size);
    case OSPREY_PRED_HOMO_SEGMENT:
    case OSPREY_PRED_ARRAY:
        result = ref_address_compare(&left->segment.a1, &right->segment.a1);
        if (result != 0) return result;
        result = ref_address_compare(&left->segment.a2, &right->segment.a2);
        return result != 0 ? result : ref_cmp_i64(left->segment.size,
                                                   right->segment.size);
    case OSPREY_PRED_ARRAY_START:
        return ref_address_compare(&left->addr, &right->addr);
    case OSPREY_PRED_FIELD_OF:
    case OSPREY_PRED_POINTER:
        result = ref_chunk_compare(&left->attached.chunk,
                                   &right->attached.chunk);
        return result != 0 ? result : ref_address_compare(
            &left->attached.base, &right->attached.base);
    default:
        return 0;
    }
}

static void ref_put_region(OspreyKey *key, const OspreyRegionId *region,
                           size_t word)
{
    key->w[word + 0] = region->kind;
    key->w[word + 1] = region->code_image_id;
    key->w[word + 2] = region->site_offset;
}

static void ref_put_address(OspreyKey *key, const OspreyAddress *address,
                            size_t word)
{
    ref_put_region(key, &address->region, word);
    key->w[word + 3] = (uint64_t)address->offset;
}

static void ref_put_chunk(OspreyKey *key, const OspreyChunk *chunk,
                          size_t word)
{
    ref_put_address(key, &chunk->address, word);
    key->w[word + 4] = chunk->size;
}

static OspreyKey ref_var_key(uint8_t kind, const OspreyVarPayload *payload)
{
    OspreyKey key;

    memset(&key, 0, sizeof(key));
    key.tag = 0x564152ULL;
    key.w[0] = kind;
    if (payload == NULL) return key;
    switch (kind) {
    case OSPREY_PRED_PRIMITIVE_VAR:
    case OSPREY_PRED_SCALAR:
        ref_put_chunk(&key, &payload->chunk, 1);
        break;
    case OSPREY_PRED_PRIMITIVE_ACCESS:
        ref_put_chunk(&key, &payload->prim_access.chunk, 1);
        key.w[6] = payload->prim_access.insn_pc;
        break;
    case OSPREY_PRED_UNFOLDABLE_HEAP:
    case OSPREY_PRED_FOLDABLE_HEAP:
        ref_put_region(&key, &payload->heap_fold.region, 1);
        key.w[4] = payload->heap_fold.size;
        break;
    case OSPREY_PRED_HOMO_SEGMENT: {
        OspreyAddress first = payload->segment.a1;
        OspreyAddress second = payload->segment.a2;
        if (ref_address_compare(&second, &first) < 0) {
            OspreyAddress swap = first;
            first = second;
            second = swap;
        }
        ref_put_address(&key, &first, 1);
        ref_put_address(&key, &second, 5);
        key.w[9] = (uint64_t)payload->segment.size;
        break;
    }
    case OSPREY_PRED_ARRAY:
        ref_put_address(&key, &payload->segment.a1, 1);
        ref_put_address(&key, &payload->segment.a2, 5);
        key.w[9] = (uint64_t)payload->segment.size;
        break;
    case OSPREY_PRED_ARRAY_START:
        ref_put_address(&key, &payload->addr, 1);
        break;
    case OSPREY_PRED_FIELD_OF:
    case OSPREY_PRED_POINTER:
        ref_put_chunk(&key, &payload->attached.chunk, 1);
        ref_put_address(&key, &payload->attached.base, 6);
        break;
    default:
        break;
    }
    return key;
}

static bool ref_key_equal(const OspreyKey *left, const OspreyKey *right)
{
    if (left->tag != right->tag) return false;
    return memcmp(left->w, right->w, sizeof(left->w)) == 0;
}

static int ref_key_compare(const OspreyKey *left, const OspreyKey *right)
{
    int result = ref_cmp_u64(left->tag, right->tag);
    if (result != 0) return result;
    for (size_t i = 0; i < G_N_ELEMENTS(left->w); i++) {
        result = ref_cmp_u64(left->w[i], right->w[i]);
        if (result != 0) return result;
    }
    return 0;
}

static OspreyFactorKey ref_factor_key(const OspreyFactor *factor,
                                      const uint32_t *local_by_graph_var)
{
    OspreyFactorKey key;

    memset(&key, 0, sizeof(key));
    key.rule = factor->rule;
    key.stage = factor->stage;
    key.potential_kind = factor->potential_kind;
    key.negative = factor->negative;
    key.head_idx = factor->head_idx;
    memcpy(&key.p_bits, &factor->p, sizeof(key.p_bits));
    key.num_vars = factor->num_vars;
    for (uint32_t i = 0; i < factor->num_vars; i++) {
        key.var_ids[i] = local_by_graph_var[factor->var_ids[i]];
    }
    return key;
}

static bool ref_factor_key_equal(const OspreyFactorKey *left,
                                 const OspreyFactorKey *right)
{
    if (left->rule != right->rule || left->stage != right->stage ||
        left->potential_kind != right->potential_kind ||
        left->negative != right->negative || left->head_idx != right->head_idx ||
        left->p_bits != right->p_bits || left->num_vars != right->num_vars ||
        left->reserved != 0 || left->reserved2 != 0 ||
        right->reserved != 0 || right->reserved2 != 0 ||
        left->num_vars > OSPREY_FACTOR_MAX_ARITY) return false;
    for (uint32_t i = 0; i < left->num_vars; i++) {
        if (left->var_ids[i] != right->var_ids[i]) return false;
    }
    return true;
}

static int ref_factor_key_compare(const OspreyFactorKey *left,
                                  const OspreyFactorKey *right)
{
    int result = ref_cmp_u64(left->stage, right->stage);
    if (result != 0) return result;
    result = ref_cmp_u64(left->rule, right->rule);
    if (result != 0) return result;
    result = ref_cmp_u64(left->potential_kind, right->potential_kind);
    if (result != 0) return result;
    result = ref_cmp_u64(left->negative, right->negative);
    if (result != 0) return result;
    result = ref_cmp_u64(left->p_bits, right->p_bits);
    if (result != 0) return result;
    result = ref_cmp_u64(left->head_idx, right->head_idx);
    if (result != 0) return result;
    result = ref_cmp_u64(left->num_vars, right->num_vars);
    if (result != 0) return result;
    for (uint32_t i = 0; i < left->num_vars; i++) {
        result = ref_cmp_u64(left->var_ids[i], right->var_ids[i]);
        if (result != 0) return result;
    }
    return 0;
}

static int ref_var_compare(const void *left_pointer,
                           const void *right_pointer)
{
    const RefVar *left = left_pointer;
    const RefVar *right = right_pointer;
    int result = ref_cmp_u64(left->kind, right->kind);

    if (result == 0) {
        result = ref_payload_compare(left->kind, &left->payload,
                                     &right->payload);
    }
    if (result == 0) result = ref_key_compare(&left->key, &right->key);
    return result != 0 ? result : ref_cmp_u64(left->graph_id,
                                               right->graph_id);
}

static int ref_factor_compare(const void *left_pointer,
                              const void *right_pointer)
{
    const RefFactor *left = left_pointer;
    const RefFactor *right = right_pointer;
    int result = ref_factor_key_compare(&left->key, &right->key);

    return result != 0 ? result : ref_cmp_u64(left->graph_id,
                                               right->graph_id);
}

static int ref_edge_compare(const void *left_pointer,
                            const void *right_pointer)
{
    const RefEdge *left = left_pointer;
    const RefEdge *right = right_pointer;
    int result = ref_factor_key_compare(&left->factor_key,
                                        &right->factor_key);
    if (result != 0) return result;
    result = ref_cmp_u64(left->factor_position, right->factor_position);
    if (result != 0) return result;
    return ref_key_compare(&left->variable_key, &right->variable_key);
}

static bool ref_union(uint32_t *parent, uint32_t count,
                      uint32_t left, uint32_t right)
{
    if (parent == NULL || left >= count || right >= count) return false;
    left = parent[left];
    while (parent[left] != left) left = parent[left];
    right = parent[right];
    while (parent[right] != right) right = parent[right];
    if (left != right) parent[right] = left;
    return true;
}

static uint32_t ref_find(uint32_t *parent, uint32_t value)
{
    uint32_t root = value;
    while (parent[root] != root) root = parent[root];
    while (parent[value] != value) {
        uint32_t next = parent[value];
        parent[value] = root;
        value = next;
    }
    return root;
}

static bool ref_add_bytes(uint64_t *total, uint64_t count,
                          size_t element_size)
{
    uint64_t bytes;

    if (count != 0 && count > UINT64_MAX / element_size) return false;
    bytes = count * element_size;
    if (UINT64_MAX - *total < bytes) return false;
    *total += bytes;
    return *total <= SIZE_MAX;
}

static bool ref_workspace_bytes(uint32_t variable_count,
                                uint32_t factor_count, uint32_t edge_count,
                                const uint32_t *component_vars,
                                const uint32_t *component_factors,
                                const uint32_t *component_edges,
                                uint32_t component_count, uint64_t *out)
{
    uint64_t total = sizeof(OspreyBpGraph);
    uint64_t message_values;

    if (out == NULL || component_vars == NULL || component_factors == NULL ||
        component_edges == NULL ||
        !ref_add_bytes(&total, 4, sizeof(GArray)) ||
        !ref_add_bytes(&total, 1, sizeof(GPtrArray)) ||
        !ref_add_bytes(&total, variable_count, sizeof(OspreyBpVarRef)) ||
        !ref_add_bytes(&total, factor_count, sizeof(OspreyBpFactorRef)) ||
        !ref_add_bytes(&total, edge_count, sizeof(OspreyBpEdge)) ||
        !ref_add_bytes(&total, edge_count, sizeof(uint32_t)) ||
        !ref_add_bytes(&total, variable_count, sizeof(uint32_t)) ||
        !ref_add_bytes(&total, factor_count, sizeof(uint32_t)) ||
        !ref_add_bytes(&total, component_count, sizeof(gpointer))) return false;
    message_values = (uint64_t)edge_count * 2u;
    for (unsigned i = 0; i < 5; i++) {
        if (!ref_add_bytes(&total, message_values, sizeof(double))) return false;
    }
    if (!ref_add_bytes(&total, (uint64_t)variable_count * 2u,
                       sizeof(double))) return false;
    for (uint32_t component = 0; component < component_count; component++) {
        if (!ref_add_bytes(&total, 1, sizeof(OspreyBpComponent)) ||
            !ref_add_bytes(&total, 3, sizeof(GArray)) ||
            !ref_add_bytes(&total, component_vars[component],
                           sizeof(uint32_t)) ||
            !ref_add_bytes(&total, component_factors[component],
                           sizeof(uint32_t)) ||
            !ref_add_bytes(&total, component_edges[component],
                           sizeof(uint32_t))) return false;
    }
    *out = total;
    return true;
}

static bool ref_double_equal(double actual, double expected)
{
    return isnan(expected) ? isnan(actual) : actual == expected;
}

static double ref_log_probability(double probability)
{
    return probability == 0.0 ? -INFINITY : log(probability);
}

static bool ref_array_range_matches(const GArray *actual, uint32_t begin,
                                    const uint32_t *expected, uint32_t count)
{
    if (actual == NULL || begin > actual->len ||
        count > actual->len - begin) return false;
    for (uint32_t i = 0; i < count; i++) {
        if (g_array_index(actual, uint32_t, begin + i) != expected[i]) {
            return false;
        }
    }
    return true;
}

bool stage5_bp_reference_matches(const OspreyContext *ctx,
                                 const OspreyBpGraph *graph)
{
    const OspreyGraph *source;
    RefVar *vars = NULL;
    RefFactor *factors = NULL;
    RefEdge *edges = NULL;
    uint32_t *local_by_graph_var = NULL;
    uint32_t *local_by_graph_factor = NULL;
    uint32_t *degrees = NULL;
    uint32_t *var_edges = NULL;
    uint32_t *var_begins = NULL;
    uint32_t *var_cursor = NULL;
    uint32_t *parent = NULL;
    uint32_t *component_for_var = NULL;
    uint32_t *component_for_factor = NULL;
    uint32_t *root_component = NULL;
    uint32_t *component_vars = NULL;
    uint32_t *component_factors = NULL;
    uint32_t *component_edges = NULL;
    uint32_t variable_count;
    uint32_t factor_count;
    uint32_t edge_count = 0;
    uint32_t component_count = 0;
    uint32_t expected_var_begin = 0;
    uint64_t expected_workspace;
    bool valid = false;

    if (ctx == NULL || graph == NULL || ctx->graph == NULL ||
        graph->vars == NULL || graph->factors == NULL ||
        graph->edges == NULL || graph->var_edges == NULL ||
        graph->components == NULL || graph->local_by_graph_var == NULL ||
        graph->local_by_graph_factor == NULL ||
        graph->msg_vf_current == NULL || graph->msg_vf_next == NULL ||
        graph->msg_fv_current == NULL || graph->msg_fv_next == NULL ||
        graph->scratch_message == NULL || graph->beliefs == NULL) return false;
    source = ctx->graph;
    if (source->vars == NULL || source->factors == NULL ||
        source->vars->data == NULL || source->factors->data == NULL ||
        source->vars->len == 0 || source->factors->len == 0 ||
        source->vars->len > UINT32_MAX || source->factors->len > UINT32_MAX) {
        return false;
    }
    variable_count = source->vars->len;
    factor_count = source->factors->len;

    vars = g_try_malloc((size_t)variable_count * sizeof(*vars));
    factors = g_try_malloc((size_t)factor_count * sizeof(*factors));
    local_by_graph_var = g_try_malloc((size_t)variable_count *
                                      sizeof(*local_by_graph_var));
    local_by_graph_factor = g_try_malloc((size_t)factor_count *
                                         sizeof(*local_by_graph_factor));
    degrees = g_try_malloc0((size_t)variable_count * sizeof(*degrees));
    parent = g_try_malloc((size_t)variable_count * sizeof(*parent));
    if (vars == NULL || factors == NULL || local_by_graph_var == NULL ||
        local_by_graph_factor == NULL || degrees == NULL || parent == NULL) {
        goto out;
    }
    for (uint32_t graph_id = 0; graph_id < variable_count; graph_id++) {
        const OspreyVar *variable = &g_array_index(source->vars, OspreyVar,
                                                   graph_id);
        if (variable->id != graph_id || variable->kind <= OSPREY_PRED_NONE ||
            variable->kind >= OSPREY_PRED_COUNT || variable->hard_false > 1 ||
            variable->region_limit_hit > 1 || variable->belief_valid > 1) goto out;
        vars[graph_id].graph_id = graph_id;
        vars[graph_id].kind = variable->kind;
        vars[graph_id].payload = variable->payload;
        vars[graph_id].key = ref_var_key(variable->kind, &variable->payload);
        parent[graph_id] = graph_id;
    }
    qsort(vars, variable_count, sizeof(*vars), ref_var_compare);
    for (uint32_t local = 0; local < variable_count; local++) {
        local_by_graph_var[vars[local].graph_id] = local;
        if (local != 0 && ref_key_equal(&vars[local - 1].key,
                                        &vars[local].key)) goto out;
    }

    for (uint32_t graph_id = 0; graph_id < factor_count; graph_id++) {
        const OspreyFactor *factor = g_array_index(
            source->factors, OspreyFactor *, graph_id);
        if (factor == NULL || factor->id != graph_id ||
            factor->num_vars == 0 ||
            factor->num_vars > OSPREY_FACTOR_MAX_ARITY ||
            factor->var_ids == NULL) goto out;
        factors[graph_id].graph_id = graph_id;
        if (factor->num_vars > UINT32_MAX - edge_count) goto out;
        edge_count += factor->num_vars;
        for (uint32_t position = 0; position < factor->num_vars; position++) {
            uint32_t graph_var = factor->var_ids[position];
            if (graph_var >= variable_count ||
                local_by_graph_var[graph_var] == UINT32_MAX ||
                degrees[graph_var] == UINT32_MAX) goto out;
            degrees[graph_var]++;
            for (uint32_t prior = 0; prior < position; prior++) {
                if (factor->var_ids[prior] == graph_var) goto out;
            }
            if (position != 0 && !ref_union(parent, variable_count,
                                             factor->var_ids[0], graph_var)) {
                goto out;
            }
        }
        factors[graph_id].key = ref_factor_key(factor,
                                               local_by_graph_var);
    }
    if (edge_count == 0) goto out;
    qsort(factors, factor_count, sizeof(*factors), ref_factor_compare);
    for (uint32_t local = 0; local < factor_count; local++) {
        local_by_graph_factor[factors[local].graph_id] = local;
        if (local != 0 && ref_factor_key_compare(&factors[local - 1].key,
                                                 &factors[local].key) == 0) {
            goto out;
        }
    }

    edges = g_try_malloc((size_t)edge_count * sizeof(*edges));
    var_edges = g_try_malloc((size_t)edge_count * sizeof(*var_edges));
    var_begins = g_try_malloc((size_t)variable_count * sizeof(*var_begins));
    var_cursor = g_try_malloc((size_t)variable_count * sizeof(*var_cursor));
    if (edges == NULL || var_edges == NULL || var_begins == NULL ||
        var_cursor == NULL) goto out;

    uint32_t edge_id = 0;
    for (uint32_t local_factor = 0; local_factor < factor_count;
         local_factor++) {
        const RefFactor *ordered = &factors[local_factor];
        const OspreyFactor *factor = g_array_index(
            source->factors, OspreyFactor *, ordered->graph_id);
        for (uint32_t position = 0; position < factor->num_vars; position++) {
            uint32_t graph_var = factor->var_ids[position];
            RefEdge *edge = &edges[edge_id];
            edge->id = edge_id;
            edge->local_var = local_by_graph_var[graph_var];
            edge->local_factor = local_factor;
            edge->factor_position = position;
            edge->graph_var_id = graph_var;
            edge->graph_factor_id = ordered->graph_id;
            edge->factor_key = ordered->key;
            edge->variable_key = vars[edge->local_var].key;
            edge_id++;
        }
    }
    if (edge_id != edge_count) goto out;

    uint32_t var_begin = 0;
    for (uint32_t local = 0; local < variable_count; local++) {
        var_begins[local] = var_begin;
        var_cursor[local] = var_begin;
        if (var_begin > edge_count - degrees[vars[local].graph_id]) goto out;
        var_begin += degrees[vars[local].graph_id];
    }
    if (var_begin != edge_count) goto out;
    for (uint32_t id = 0; id < edge_count; id++) {
        uint32_t local = edges[id].local_var;
        var_edges[var_cursor[local]++] = id;
    }
    for (uint32_t local = 0; local < variable_count; local++) {
        uint32_t begin = var_begins[local];
        uint32_t count = degrees[vars[local].graph_id];
        for (uint32_t i = 1; i < count; i++) {
            uint32_t value = var_edges[begin + i];
            uint32_t j = i;
            while (j > 0 && ref_edge_compare(
                       &edges[var_edges[begin + j - 1]], &edges[value]) > 0) {
                var_edges[begin + j] = var_edges[begin + j - 1];
                j--;
            }
            var_edges[begin + j] = value;
        }
    }

    component_for_var = g_try_malloc((size_t)variable_count *
                                      sizeof(*component_for_var));
    component_for_factor = g_try_malloc((size_t)factor_count *
                                        sizeof(*component_for_factor));
    root_component = g_try_malloc((size_t)variable_count *
                                  sizeof(*root_component));
    if (component_for_var == NULL || component_for_factor == NULL ||
        root_component == NULL) goto out;
    for (uint32_t local = 0; local < variable_count; local++) {
        root_component[local] = UINT32_MAX;
    }
    for (uint32_t local = 0; local < variable_count; local++) {
        uint32_t root = ref_find(parent, vars[local].graph_id);
        if (root_component[root] == UINT32_MAX) {
            root_component[root] = component_count++;
        }
        component_for_var[local] = root_component[root];
    }
    for (uint32_t local_factor = 0; local_factor < factor_count;
         local_factor++) {
        component_for_factor[local_factor] = component_for_var[
            factors[local_factor].key.var_ids[0]];
    }
    component_vars = g_try_malloc0((size_t)component_count *
                                   sizeof(*component_vars));
    component_factors = g_try_malloc0((size_t)component_count *
                                      sizeof(*component_factors));
    component_edges = g_try_malloc0((size_t)component_count *
                                    sizeof(*component_edges));
    if (component_vars == NULL || component_factors == NULL ||
        component_edges == NULL) goto out;
    for (uint32_t local = 0; local < variable_count; local++) {
        component_vars[component_for_var[local]]++;
    }
    for (uint32_t local_factor = 0; local_factor < factor_count;
         local_factor++) {
        component_factors[component_for_factor[local_factor]]++;
    }
    for (uint32_t id = 0; id < edge_count; id++) {
        component_edges[component_for_var[edges[id].local_var]]++;
    }

    if (graph->vars->len != variable_count ||
        graph->factors->len != factor_count || graph->edges->len != edge_count ||
        graph->var_edges->len != edge_count ||
        graph->components->len != component_count) goto out;
    for (uint32_t graph_id = 0; graph_id < variable_count; graph_id++) {
        if (graph->local_by_graph_var[graph_id] !=
            local_by_graph_var[graph_id]) goto out;
    }
    for (uint32_t graph_id = 0; graph_id < factor_count; graph_id++) {
        if (graph->local_by_graph_factor[graph_id] !=
            local_by_graph_factor[graph_id]) goto out;
    }
    for (uint32_t local = 0; local < variable_count; local++) {
        const OspreyBpVarRef *actual = &g_array_index(
            graph->vars, OspreyBpVarRef, local);
        const OspreyVar *source_var = &g_array_index(
            source->vars, OspreyVar, vars[local].graph_id);
        uint32_t expected_count = degrees[vars[local].graph_id];
        uint32_t expected_begin = 0;
        if (local != 0) {
            for (uint32_t prior = 0; prior < local; prior++) {
                expected_begin += degrees[vars[prior].graph_id];
            }
        }
        if (actual->graph_var_id != vars[local].graph_id ||
            actual->var_edge_begin != expected_begin ||
            actual->var_edge_count != expected_count ||
            actual->reserved[0] != 0 || actual->reserved[1] != 0 ||
            actual->reserved[2] != 0 ||
            actual->base_seed_valid != source_var->belief_valid) goto out;
        if (actual->base_seed_valid) {
            if (!isfinite(source_var->belief) || source_var->belief < 0.0 ||
                source_var->belief > 1.0 ||
                actual->base_seed[1] != source_var->belief ||
                actual->base_seed[0] != 1.0 - source_var->belief) goto out;
        } else if (!isnan(actual->base_seed[0]) ||
                   !isnan(actual->base_seed[1])) goto out;
    }
    for (uint32_t local_factor = 0; local_factor < factor_count;
         local_factor++) {
        const OspreyBpFactorRef *actual = &g_array_index(
            graph->factors, OspreyBpFactorRef, local_factor);
        const OspreyFactor *factor = g_array_index(
            source->factors, OspreyFactor *, factors[local_factor].graph_id);
        uint32_t expected_begin = 0;
        for (uint32_t prior = 0; prior < local_factor; prior++) {
            const OspreyFactor *prior_factor = g_array_index(
                source->factors, OspreyFactor *, factors[prior].graph_id);
            expected_begin += prior_factor->num_vars;
        }
        if (actual->graph_factor_id != factors[local_factor].graph_id ||
            actual->factor_edge_begin != expected_begin ||
            actual->factor_edge_count != factor->num_vars) goto out;
    }
    for (uint32_t id = 0; id < edge_count; id++) {
        const OspreyBpEdge *actual = &g_array_index(graph->edges,
                                                    OspreyBpEdge, id);
        const RefEdge *expected = &edges[id];
        if (actual->id != expected->id ||
            actual->local_var != expected->local_var ||
            actual->local_factor != expected->local_factor ||
            actual->factor_position != expected->factor_position ||
            actual->graph_var_id != expected->graph_var_id ||
            actual->graph_factor_id != expected->graph_factor_id ||
            actual->key.factor_position != expected->factor_position ||
            actual->key.reserved != 0 ||
            !ref_factor_key_equal(&actual->key.factor,
                                  &expected->factor_key) ||
            !ref_key_equal(&actual->key.variable, &expected->variable_key)) {
            goto out;
        }
    }
    for (uint32_t local = 0; local < variable_count; local++) {
        const OspreyBpVarRef *actual = &g_array_index(
            graph->vars, OspreyBpVarRef, local);
        uint32_t begin = actual->var_edge_begin;
        uint32_t count = actual->var_edge_count;
        if (begin > edge_count || count > edge_count - begin ||
            begin != expected_var_begin ||
            !ref_array_range_matches(graph->var_edges, begin,
                                     var_edges + begin, count)) {
            goto out;
        }
        for (uint32_t i = 0; i < count; i++) {
            uint32_t edge_id_at_range = g_array_index(
                graph->var_edges, uint32_t, begin + i);
            if (edges[edge_id_at_range].local_var != local ||
                (i != 0 && ref_edge_compare(
                    &edges[g_array_index(graph->var_edges, uint32_t,
                                         begin + i - 1)],
                    &edges[edge_id_at_range]) >= 0)) goto out;
        }
        expected_var_begin += count;
    }
    if (expected_var_begin != edge_count) goto out;

    for (uint32_t component = 0; component < component_count; component++) {
        const OspreyBpComponent *actual = g_ptr_array_index(
            graph->components, component);
        uint32_t var_index = 0;
        uint32_t factor_index = 0;
        uint32_t edge_index = 0;
        if (actual == NULL || actual->id != component ||
            actual->local_vars == NULL || actual->local_factors == NULL ||
            actual->edges == NULL ||
            actual->local_vars->len != component_vars[component] ||
            actual->local_factors->len != component_factors[component] ||
            actual->edges->len != component_edges[component]) goto out;
        for (uint32_t local = 0; local < variable_count; local++) {
            if (component_for_var[local] == component &&
                g_array_index(actual->local_vars, uint32_t, var_index++) !=
                    local) goto out;
        }
        for (uint32_t local_factor = 0; local_factor < factor_count;
             local_factor++) {
            if (component_for_factor[local_factor] == component &&
                g_array_index(actual->local_factors, uint32_t, factor_index++) !=
                    local_factor) goto out;
        }
        for (uint32_t id = 0; id < edge_count; id++) {
            if (component_for_var[edges[id].local_var] == component &&
                g_array_index(actual->edges, uint32_t, edge_index++) != id) {
                goto out;
            }
        }
        if (var_index != component_vars[component] ||
            factor_index != component_factors[component] ||
            edge_index != component_edges[component]) goto out;
    }

    if (graph->message_values != (uint64_t)edge_count * 2u ||
        graph->workspace_limit != (ctx->config.max_bp_table_bytes == 0
                                    ? 256ULL * 1024ULL * 1024ULL
                                    : ctx->config.max_bp_table_bytes) ||
        !ref_workspace_bytes(variable_count, factor_count, edge_count,
                             component_vars, component_factors, component_edges,
                             component_count, &expected_workspace) ||
        graph->workspace_bytes != expected_workspace) goto out;
    for (uint32_t id = 0; id < edge_count; id++) {
        const OspreyBpEdge *edge = &g_array_index(graph->edges,
                                                  OspreyBpEdge, id);
        const OspreyVar *variable = &g_array_index(
            source->vars, OspreyVar, vars[edge->local_var].graph_id);
        double expected_zero = 0.5;
        double expected_one = 0.5;
        size_t index = (size_t)id * 2u;
        if (variable->belief_valid) {
            expected_zero = 1.0 - variable->belief;
            expected_one = variable->belief;
        }
        expected_zero = ref_log_probability(expected_zero);
        expected_one = ref_log_probability(expected_one);
        if (!ref_double_equal(graph->msg_vf_current[index], expected_zero) ||
            !ref_double_equal(graph->msg_vf_current[index + 1], expected_one) ||
            graph->msg_fv_current[index] != -log(2.0)) goto out;
    }
    for (uint64_t i = 0; i < graph->message_values; i++) {
        if (!isnan(graph->msg_vf_next[i]) ||
            !isnan(graph->msg_fv_next[i]) ||
            !isnan(graph->scratch_message[i])) goto out;
    }
    for (uint64_t i = 0; i < (uint64_t)variable_count * 2u; i++) {
        if (!isnan(graph->beliefs[i])) goto out;
    }
    valid = true;
out:
    g_free(vars);
    g_free(factors);
    g_free(edges);
    g_free(local_by_graph_var);
    g_free(local_by_graph_factor);
    g_free(degrees);
    g_free(var_edges);
    g_free(var_begins);
    g_free(var_cursor);
    g_free(parent);
    g_free(component_for_var);
    g_free(component_for_factor);
    g_free(root_component);
    g_free(component_vars);
    g_free(component_factors);
    g_free(component_edges);
    return valid;
}

/* ------------------------------------------------------------------ */
/* Independent Stage 5.2 numerical oracle                             */
/* ------------------------------------------------------------------ */

static bool ref_round_log_value_valid(double value)
{
    return isfinite(value) || value == -INFINITY;
}

static bool ref_round_logaddexp(double left, double right, double *out)
{
    double high;
    double low;
    double value;

    if (out == NULL || !ref_round_log_value_valid(left) ||
        !ref_round_log_value_valid(right)) return false;
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

static bool ref_round_log_product_add(double left, double right, double *out)
{
    double value;

    if (out == NULL || !ref_round_log_value_valid(left) ||
        !ref_round_log_value_valid(right)) return false;
    if (left == -INFINITY || right == -INFINITY) {
        *out = -INFINITY;
        return true;
    }
    value = left + right;
    if (!isfinite(value)) return false;
    *out = value;
    return true;
}

static bool ref_round_log_normalize(double pair[2])
{
    double norm;

    if (pair == NULL || !ref_round_log_value_valid(pair[0]) ||
        !ref_round_log_value_valid(pair[1]) ||
        (pair[0] == -INFINITY && pair[1] == -INFINITY) ||
        !ref_round_logaddexp(pair[0], pair[1], &norm) ||
        !isfinite(norm)) return false;
    for (unsigned i = 0; i < 2; i++) {
        double normalized;
        if (pair[i] == -INFINITY) continue;
        normalized = pair[i] - norm;
        if (!isfinite(normalized) || normalized > 0.0) return false;
        pair[i] = normalized;
    }
    return true;
}

static bool ref_round_pair_valid(const double pair[2])
{
    double norm;

    return pair != NULL && ref_round_log_value_valid(pair[0]) &&
           ref_round_log_value_valid(pair[1]) &&
           !(pair[0] == -INFINITY && pair[1] == -INFINITY) &&
           ref_round_logaddexp(pair[0], pair[1], &norm) &&
           isfinite(norm) && fabs(norm) <= 1e-12;
}

static void ref_round_clear_next(OspreyBpMessages *messages,
                                 uint64_t value_count)
{
    if (messages == NULL || messages->vf_next == NULL ||
        messages->fv_next == NULL) return;
    for (uint64_t i = 0; i < value_count; i++) {
        messages->vf_next[(size_t)i] = NAN;
        messages->fv_next[(size_t)i] = NAN;
    }
}

static bool ref_round_find_factor_edge(const OspreyBpGraph *graph,
                                       uint32_t local_factor,
                                       uint32_t position,
                                       uint32_t *edge_id_out)
{
    uint32_t found = UINT32_MAX;

    if (graph == NULL || graph->edges == NULL || edge_id_out == NULL) {
        return false;
    }
    for (uint32_t edge_id = 0; edge_id < graph->edges->len; edge_id++) {
        const OspreyBpEdge *edge = &g_array_index(graph->edges,
                                                  OspreyBpEdge, edge_id);
        if (edge->local_factor != local_factor ||
            edge->factor_position != position) continue;
        if (found != UINT32_MAX) return false;
        found = edge_id;
    }
    if (found == UINT32_MAX) return false;
    *edge_id_out = found;
    return true;
}

static bool ref_round_graph_valid(const OspreyContext *ctx,
                                  const OspreyBpGraph *graph,
                                  uint32_t *edge_count_out)
{
    const OspreyGraph *source;
    uint32_t edge_count;

    if (ctx == NULL || graph == NULL || ctx->graph == NULL ||
        graph->edges == NULL || graph->factors == NULL ||
        graph->edges->data == NULL || graph->factors->data == NULL ||
        graph->edges->len == 0 || graph->edges->len > UINT32_MAX ||
        graph->factors->len == 0 || graph->factors->len > UINT32_MAX ||
        graph->vars == NULL || graph->vars->len == 0 ||
        graph->vars->len > UINT32_MAX || edge_count_out == NULL) return false;
    source = ctx->graph;
    if (source->factors == NULL || source->vars == NULL ||
        source->factors->data == NULL || source->vars->data == NULL ||
        source->factors->len != graph->factors->len ||
        source->vars->len != graph->vars->len) return false;
    edge_count = graph->edges->len;
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        const OspreyBpEdge *edge = &g_array_index(graph->edges,
                                                  OspreyBpEdge, edge_id);
        if (edge->id != edge_id || edge->local_factor >= graph->factors->len ||
            edge->local_var >= graph->vars->len) return false;
    }
    for (uint32_t local_factor = 0; local_factor < graph->factors->len;
         local_factor++) {
        const OspreyBpFactorRef *factor_ref = &g_array_index(
            graph->factors, OspreyBpFactorRef, local_factor);
        const OspreyFactor *factor;

        if (factor_ref->graph_factor_id >= source->factors->len) return false;
        factor = g_array_index(source->factors, OspreyFactor *,
                               factor_ref->graph_factor_id);
        if (factor == NULL || factor->num_vars == 0 ||
            factor->num_vars > OSPREY_FACTOR_MAX_ARITY) return false;
        for (uint32_t position = 0; position < factor->num_vars; position++) {
            uint32_t edge_id;
            if (!ref_round_find_factor_edge(graph, local_factor, position,
                                            &edge_id)) return false;
            if (g_array_index(graph->edges, OspreyBpEdge, edge_id)
                    .graph_factor_id != factor_ref->graph_factor_id) {
                return false;
            }
        }
    }
    *edge_count_out = edge_count;
    return true;
}

OspreyStatus stage5_bp_reference_compute_factor_half(
    const OspreyContext *ctx, const OspreyBpGraph *graph,
    const double *vf_messages, double *fv_messages)
{
    uint32_t edge_count;
    uint64_t value_count;
    OspreyStatus status;

    if (!ref_round_graph_valid(ctx, graph, &edge_count) ||
        vf_messages == NULL || fv_messages == NULL) {
        return OSPREY_INVALID_GRAPH;
    }
    value_count = (uint64_t)edge_count * 2u;
    if (graph->message_values != value_count || value_count > SIZE_MAX) {
        return OSPREY_INVALID_GRAPH;
    }
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        if (!ref_round_pair_valid(&vf_messages[(size_t)edge_id * 2u])) {
            return OSPREY_INVALID_GRAPH;
        }
    }
    for (uint64_t i = 0; i < value_count; i++) {
        fv_messages[(size_t)i] = NAN;
    }

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
                    if (!ref_round_find_factor_edge(graph, edge->local_factor,
                                                    position, &incoming_id)) {
                        status = OSPREY_INVALID_GRAPH;
                        goto fail;
                    }
                    incoming = &vf_messages[(size_t)incoming_id * 2u];
                    if (!ref_round_log_product_add(
                            term, incoming[assignment[position]], &term)) {
                        status = OSPREY_INVALID_GRAPH;
                        goto fail;
                    }
                }
                if (!ref_round_logaddexp(raw, term, &raw)) {
                    status = OSPREY_INVALID_GRAPH;
                    goto fail;
                }
            }
            output[recipient_state] = raw;
        }
        if (!ref_round_log_normalize(output)) {
            status = (output[0] == -INFINITY && output[1] == -INFINITY)
                ? OSPREY_INVALID_MODEL : OSPREY_INVALID_GRAPH;
            goto fail;
        }
        fv_messages[(size_t)edge_id * 2u] = output[0];
        fv_messages[(size_t)edge_id * 2u + 1u] = output[1];
    }
    return OSPREY_OK;

fail:
    for (uint64_t i = 0; i < value_count; i++) {
        fv_messages[(size_t)i] = NAN;
    }
    return status;
}

static OspreyStatus ref_round_compute_variable_half(
    const OspreyContext *ctx, const OspreyBpGraph *graph,
    const double *fv_current, double *vf_next)
{
    uint32_t edge_count;
    uint64_t value_count;
    OspreyStatus status = OSPREY_INVALID_GRAPH;

    if (!ref_round_graph_valid(ctx, graph, &edge_count) ||
        fv_current == NULL || vf_next == NULL) return OSPREY_INVALID_GRAPH;
    value_count = (uint64_t)edge_count * 2u;
    if (graph->message_values != value_count || value_count > SIZE_MAX) {
        return OSPREY_INVALID_GRAPH;
    }
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        if (!ref_round_pair_valid(&fv_current[(size_t)edge_id * 2u])) {
            return OSPREY_INVALID_GRAPH;
        }
    }
    for (uint64_t i = 0; i < value_count; i++) vf_next[(size_t)i] = NAN;

    /* Scan semantic edges instead of the production variable CSR. */
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        const OspreyBpEdge *edge = &g_array_index(graph->edges,
                                                  OspreyBpEdge, edge_id);
        double output[2] = { 0.0, 0.0 };

        for (uint32_t incoming_id = 0; incoming_id < edge_count;
             incoming_id++) {
            const OspreyBpEdge *incoming = &g_array_index(
                graph->edges, OspreyBpEdge, incoming_id);
            const double *message;
            if (incoming_id == edge_id ||
                incoming->local_var != edge->local_var) continue;
            message = &fv_current[(size_t)incoming_id * 2u];
            if (!ref_round_log_product_add(output[0], message[0], &output[0]) ||
                !ref_round_log_product_add(output[1], message[1], &output[1])) {
                goto fail;
            }
        }
        if (!ref_round_log_normalize(output)) {
            status = (output[0] == -INFINITY && output[1] == -INFINITY)
                ? OSPREY_INVALID_MODEL : OSPREY_INVALID_GRAPH;
            goto fail;
        }
        vf_next[(size_t)edge_id * 2u] = output[0];
        vf_next[(size_t)edge_id * 2u + 1u] = output[1];
    }
    return OSPREY_OK;

fail:
    for (uint64_t i = 0; i < value_count; i++) vf_next[(size_t)i] = NAN;
    return status;
}

OspreyStatus stage5_bp_reference_compute_round(
    const OspreyContext *ctx, const OspreyBpGraph *graph,
    OspreyBpMessages *messages)
{
    uint32_t edge_count;
    uint64_t value_count;
    OspreyStatus status;

    if (!ref_round_graph_valid(ctx, graph, &edge_count) ||
        !messages || !messages->vf_current || !messages->vf_next ||
        !messages->fv_current || !messages->fv_next) {
        return OSPREY_INVALID_GRAPH;
    }
    value_count = (uint64_t)edge_count * 2u;
    if (messages->value_count != value_count || value_count > SIZE_MAX ||
        graph->message_values != value_count) return OSPREY_INVALID_GRAPH;
    for (uint32_t edge_id = 0; edge_id < edge_count; edge_id++) {
        if (!ref_round_pair_valid(&messages->vf_current[
                                      (size_t)edge_id * 2u]) ||
            !ref_round_pair_valid(&messages->fv_current[
                                      (size_t)edge_id * 2u])) {
            return OSPREY_INVALID_GRAPH;
        }
    }
    ref_round_clear_next(messages, value_count);

    status = ref_round_compute_variable_half(
        ctx, graph, messages->fv_current, messages->vf_next);
    if (status != OSPREY_OK) goto fail;
    status = stage5_bp_reference_compute_factor_half(
        ctx, graph, messages->vf_next, messages->fv_next);
    if (status != OSPREY_OK) goto fail;
    return OSPREY_OK;

fail:
    ref_round_clear_next(messages, value_count);
    return status;
}

static bool ref_round_damp_pair(const double current[2],
                                const double raw[2], double coefficient,
                                double out[2])
{
    double log_current;
    double log_raw;
    double mixed[2];

    if (current == NULL || raw == NULL || out == NULL ||
        !isfinite(coefficient) || coefficient < 0.0 || coefficient > 1.0 ||
        !ref_round_pair_valid(current) || !ref_round_pair_valid(raw)) {
        return false;
    }
    if (coefficient == 1.0) {
        memcpy(out, current, sizeof(mixed));
        return true;
    }
    if (coefficient == 0.0) {
        memcpy(out, raw, sizeof(mixed));
        return true;
    }
    log_current = log(coefficient);
    log_raw = log1p(-coefficient);
    for (unsigned state = 0; state < 2; state++) {
        double current_term = current[state] == -INFINITY
            ? -INFINITY : log_current + current[state];
        double raw_term = raw[state] == -INFINITY
            ? -INFINITY : log_raw + raw[state];
        if (!ref_round_logaddexp(current_term, raw_term, &mixed[state])) {
            return false;
        }
    }
    if (!ref_round_log_normalize(mixed)) return false;
    memcpy(out, mixed, sizeof(mixed));
    return true;
}

OspreyStatus stage5_bp_reference_compute_round_damped(
    const OspreyContext *ctx, const OspreyBpGraph *graph,
    OspreyBpMessages *messages, double coefficient)
{
    double *raw_vf = NULL;
    double *raw_fv = NULL;
    uint64_t value_count;
    OspreyStatus status = OSPREY_INVALID_GRAPH;

    if (graph == NULL || messages == NULL || messages->vf_current == NULL ||
        messages->vf_next == NULL || messages->fv_current == NULL ||
        messages->fv_next == NULL || !isfinite(coefficient) ||
        coefficient < 0.0 || coefficient > 1.0) {
        return OSPREY_INVALID_GRAPH;
    }
    value_count = graph->message_values;
    if (messages->value_count != value_count ||
        value_count > G_MAXSIZE / sizeof(double)) {
        return OSPREY_INVALID_GRAPH;
    }
    raw_vf = g_try_new(double, (gsize)value_count);
    raw_fv = g_try_new(double, (gsize)value_count);
    if (raw_vf == NULL || raw_fv == NULL) goto fail;
    status = ref_round_compute_variable_half(
        ctx, graph, messages->fv_current, raw_vf);
    if (status != OSPREY_OK) goto fail;
    for (guint edge_id = 0; edge_id < graph->edges->len; edge_id++) {
        size_t index = (size_t)edge_id * 2u;
        if (!ref_round_damp_pair(&messages->vf_current[index],
                                 &raw_vf[index], coefficient,
                                 &messages->vf_next[index])) {
            status = OSPREY_INVALID_GRAPH;
            goto fail;
        }
    }
    status = stage5_bp_reference_compute_factor_half(
        ctx, graph, messages->vf_next, raw_fv);
    if (status != OSPREY_OK) goto fail;
    for (guint edge_id = 0; edge_id < graph->edges->len; edge_id++) {
        size_t index = (size_t)edge_id * 2u;
        if (!ref_round_damp_pair(&messages->fv_current[index],
                                 &raw_fv[index], coefficient,
                                 &messages->fv_next[index])) {
            status = OSPREY_INVALID_GRAPH;
            goto fail;
        }
    }
    g_free(raw_vf);
    g_free(raw_fv);
    return OSPREY_OK;

fail:
    ref_round_clear_next(messages, value_count);
    g_free(raw_vf);
    g_free(raw_fv);
    return status;
}

/* ------------------------------------------------------------------ */
/* Independent bounded tree/forest enumerator                          */
/* ------------------------------------------------------------------ */

static bool ref_tree_logaddexp(long double left, long double right,
                               long double *out)
{
    long double high;
    long double low;

    if (out == NULL || (left != -INFINITY && !isfinite(left)) ||
        (right != -INFINITY && !isfinite(right))) return false;
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
    *out = high + log1pl(expl(low - high));
    return isfinite(*out);
}

bool stage5_bp_reference_beliefs(const OspreyContext *ctx,
                                 const OspreyBpGraph *graph,
                                 double *beliefs_out, double *logz_out)
{
    RefVar vars[12];
    uint32_t local_by_graph_var[12];
    long double true_log[12];
    long double total_log = -INFINITY;
    uint32_t variable_count;
    uint32_t assignment_count;

    if (ctx == NULL || ctx->graph == NULL || ctx->graph->vars == NULL ||
        ctx->graph->factors == NULL || graph == NULL || graph->vars == NULL ||
        beliefs_out == NULL || logz_out == NULL ||
        ctx->graph->vars->len == 0 || ctx->graph->vars->len > 12 ||
        ctx->graph->vars->len != graph->vars->len) return false;
    variable_count = ctx->graph->vars->len;
    assignment_count = 1u << variable_count;
    for (uint32_t graph_id = 0; graph_id < variable_count; graph_id++) {
        const OspreyVar *variable = &g_array_index(
            ctx->graph->vars, OspreyVar, graph_id);

        if (variable->id != graph_id ||
            variable->kind <= OSPREY_PRED_NONE ||
            variable->kind >= OSPREY_PRED_COUNT) return false;
        vars[graph_id].graph_id = graph_id;
        vars[graph_id].kind = variable->kind;
        vars[graph_id].payload = variable->payload;
        vars[graph_id].key = ref_var_key(variable->kind, &variable->payload);
    }
    qsort(vars, variable_count, sizeof(*vars), ref_var_compare);
    for (uint32_t local = 0; local < variable_count; local++) {
        const OspreyBpVarRef *projected = &g_array_index(
            graph->vars, OspreyBpVarRef, local);

        if ((local != 0 && ref_key_equal(&vars[local - 1].key,
                                         &vars[local].key)) ||
            projected->graph_var_id != vars[local].graph_id) return false;
        local_by_graph_var[vars[local].graph_id] = local;
        true_log[local] = -INFINITY;
    }

    for (uint32_t mask = 0; mask < assignment_count; mask++) {
        long double assignment_log = 0.0L;
        bool supported = true;

        for (guint factor_index = 0;
             factor_index < ctx->graph->factors->len; factor_index++) {
            const OspreyFactor *factor = g_array_index(
                ctx->graph->factors, OspreyFactor *, factor_index);
            uint8_t assignment[OSPREY_FACTOR_MAX_ARITY];
            double factor_log;

            if (factor == NULL || factor->num_vars == 0 ||
                factor->num_vars > OSPREY_FACTOR_MAX_ARITY) return false;
            for (uint32_t position = 0; position < factor->num_vars;
                 position++) {
                uint32_t graph_var = factor->var_ids[position];
                uint32_t local;
                if (graph_var >= ctx->graph->vars->len) return false;
                local = local_by_graph_var[graph_var];
                if (local >= variable_count) return false;
                assignment[position] = (uint8_t)((mask >> local) & 1u);
            }
            if (!osprey_factor_log_weight(factor, assignment, &factor_log)) {
                return false;
            }
            if (factor_log == -INFINITY) {
                supported = false;
                break;
            }
            if (!isfinite(factor_log)) return false;
            assignment_log += (long double)factor_log;
            if (!isfinite(assignment_log)) return false;
        }
        if (!supported) continue;
        if (!ref_tree_logaddexp(total_log, assignment_log, &total_log)) {
            return false;
        }
        for (uint32_t local = 0; local < variable_count; local++) {
            if (((mask >> local) & 1u) != 0 &&
                !ref_tree_logaddexp(true_log[local], assignment_log,
                                    &true_log[local])) return false;
        }
    }
    if (!isfinite(total_log)) return false;
    *logz_out = (double)total_log;
    if (!isfinite(*logz_out)) return false;
    for (uint32_t local = 0; local < variable_count; local++) {
        beliefs_out[local] = true_log[local] == -INFINITY
            ? 0.0 : (double)expl(true_log[local] - total_log);
        if (!isfinite(beliefs_out[local]) || beliefs_out[local] < 0.0 ||
            beliefs_out[local] > 1.0) return false;
    }
    return true;
}

/* ------------------------------------------------------------------ */
/* Independent Stage 5.5 bounded closure oracle                        */
/* ------------------------------------------------------------------ */

typedef struct RefClosureVar {
    OspreyKey key;
    uint64_t direct_support;
    uint64_t source_rule_bits;
    uint64_t prior_bits;
} RefClosureVar;

typedef struct RefClosureFactor {
    uint16_t rule;
    uint16_t head_idx;
    uint8_t stage;
    uint8_t potential_kind;
    uint8_t negative;
    uint8_t reserved;
    uint64_t probability_bits;
    uint32_t num_vars;
    OspreyKey vars[OSPREY_FACTOR_MAX_ARITY];
} RefClosureFactor;

static bool ref_closure_add_i64(int64_t left, int64_t right, int64_t *out)
{
    if (out == NULL || (right > 0 && left > INT64_MAX - right) ||
        (right < 0 && left < INT64_MIN - right)) return false;
    *out = left + right;
    return true;
}

static bool ref_closure_interval(uint64_t extent, int64_t lo, int64_t hi)
{
    return lo >= 0 && lo <= hi && (uint64_t)hi <= extent;
}

bool stage5_bp_reference_closure_eligible(
    const Stage5BpClosureCase *description, int64_t *folded_offset_out)
{
    int64_t prefix;
    int64_t fold;
    int64_t width;
    int64_t threshold;
    int64_t relative;
    int64_t folded;
    int64_t source_end;
    int64_t folded_end;

    if (folded_offset_out != NULL) *folded_offset_out = 0;
    if (description == NULL || folded_offset_out == NULL ||
        description->region.kind != OSPREY_REGION_HEAP_SITE ||
        !isfinite(description->primitive_probability) ||
        !isfinite(description->prefix_probability) ||
        !isfinite(description->fold_probability) ||
        description->primitive_probability <= 0.5 ||
        description->prefix_probability <= 0.5 ||
        description->fold_probability <= 0.5 ||
        description->width == 0 || description->width > INT64_MAX ||
        description->prefix_size > INT64_MAX ||
        description->fold_size == 0 ||
        description->fold_size > INT64_MAX) return false;
    prefix = (int64_t)description->prefix_size;
    fold = (int64_t)description->fold_size;
    width = (int64_t)description->width;
    if (!ref_closure_add_i64(prefix, fold, &threshold) ||
        description->source_offset < threshold ||
        !ref_closure_add_i64(description->source_offset, -prefix,
                             &relative) ||
        relative < 0 ||
        !ref_closure_add_i64(prefix, relative % fold, &folded) ||
        folded == description->source_offset ||
        !ref_closure_add_i64(description->source_offset, width,
                             &source_end) ||
        !ref_closure_add_i64(folded, width, &folded_end) ||
        !ref_closure_interval(description->extent, 0, prefix) ||
        !ref_closure_interval(description->extent, prefix, threshold) ||
        !ref_closure_interval(description->extent,
                              description->source_offset, source_end) ||
        !ref_closure_interval(description->extent, folded, folded_end)) {
        return false;
    }
    *folded_offset_out = folded;
    return true;
}

static int ref_closure_var_compare(const void *left_pointer,
                                   const void *right_pointer)
{
    const RefClosureVar *left = left_pointer;
    const RefClosureVar *right = right_pointer;
    return ref_key_compare(&left->key, &right->key);
}

static int ref_closure_factor_compare(const void *left_pointer,
                                      const void *right_pointer)
{
    const RefClosureFactor *left = left_pointer;
    const RefClosureFactor *right = right_pointer;
    int result = ref_cmp_u64(left->stage, right->stage);
    if (result != 0) return result;
    result = ref_cmp_u64(left->rule, right->rule);
    if (result != 0) return result;
    result = ref_cmp_u64(left->potential_kind, right->potential_kind);
    if (result != 0) return result;
    result = ref_cmp_u64(left->negative, right->negative);
    if (result != 0) return result;
    result = ref_cmp_u64(left->probability_bits, right->probability_bits);
    if (result != 0) return result;
    result = ref_cmp_u64(left->head_idx, right->head_idx);
    if (result != 0) return result;
    result = ref_cmp_u64(left->num_vars, right->num_vars);
    if (result != 0) return result;
    for (uint32_t i = 0; i < left->num_vars; i++) {
        result = ref_key_compare(&left->vars[i], &right->vars[i]);
        if (result != 0) return result;
    }
    return 0;
}

static OspreyKey ref_closure_payload_key(uint8_t kind,
                                         const OspreyVarPayload *payload)
{
    return ref_var_key(kind, payload);
}

static void ref_closure_var_add(RefClosureVar *vars, uint32_t *count,
                                uint8_t kind,
                                const OspreyVarPayload *payload,
                                uint64_t direct_support, double prior,
                                uint16_t source_rule)
{
    RefClosureVar *entry = &vars[(*count)++];
    memset(entry, 0, sizeof(*entry));
    entry->key = ref_closure_payload_key(kind, payload);
    entry->direct_support = direct_support;
    if (source_rule != OSPREY_RULE_NONE) {
        entry->source_rule_bits = UINT64_C(1) << source_rule;
    }
    memcpy(&entry->prior_bits, &prior, sizeof(entry->prior_bits));
}

static void ref_closure_factor_add(RefClosureFactor *factors,
                                   uint32_t *count, uint16_t rule,
                                   uint8_t stage, uint8_t potential_kind,
                                   bool negative, double probability,
                                   uint16_t head_idx,
                                   const OspreyKey *vars,
                                   uint32_t num_vars)
{
    RefClosureFactor *entry = &factors[(*count)++];
    memset(entry, 0, sizeof(*entry));
    entry->rule = rule;
    entry->stage = stage;
    entry->potential_kind = potential_kind;
    entry->negative = negative;
    entry->head_idx = head_idx;
    entry->num_vars = num_vars;
    memcpy(&entry->probability_bits, &probability,
           sizeof(entry->probability_bits));
    memcpy(entry->vars, vars, num_vars * sizeof(*vars));
}

static bool ref_closure_var_matches(const OspreyVar *actual,
                                    const RefClosureVar *expected)
{
    OspreyKey key;
    uint64_t prior_bits;

    if (actual == NULL || expected == NULL || !actual->belief_valid ||
        !isfinite(actual->belief) || actual->belief < 0.0 ||
        actual->belief > 1.0 || actual->hard_false ||
        actual->region_limit_hit) return false;
    key = ref_var_key(actual->kind, &actual->payload);
    memcpy(&prior_bits, &actual->prior, sizeof(prior_bits));
    return ref_key_equal(&key, &expected->key) &&
           actual->direct_support == expected->direct_support &&
           actual->source_rule_bits == expected->source_rule_bits &&
           prior_bits == expected->prior_bits;
}

static bool ref_closure_factor_from_actual(const OspreyContext *ctx,
                                           const OspreyFactor *factor,
                                           RefClosureFactor *out)
{
    if (ctx == NULL || ctx->graph == NULL || factor == NULL || out == NULL ||
        factor->num_vars == 0 ||
        factor->num_vars > OSPREY_FACTOR_MAX_ARITY ||
        factor->var_ids == NULL) return false;
    memset(out, 0, sizeof(*out));
    out->rule = factor->rule;
    out->stage = factor->stage;
    out->potential_kind = factor->potential_kind;
    out->negative = factor->negative;
    out->head_idx = factor->head_idx;
    out->num_vars = factor->num_vars;
    memcpy(&out->probability_bits, &factor->p,
           sizeof(out->probability_bits));
    for (uint32_t i = 0; i < factor->num_vars; i++) {
        const OspreyVar *variable;
        if (factor->var_ids[i] >= ctx->graph->vars->len) return false;
        variable = &g_array_index(ctx->graph->vars, OspreyVar,
                                  factor->var_ids[i]);
        out->vars[i] = ref_var_key(variable->kind, &variable->payload);
    }
    return true;
}

bool stage5_bp_reference_closure_matches(
    const OspreyContext *ctx, const Stage5BpClosureCase *description)
{
    RefClosureVar expected_vars[8];
    RefClosureFactor expected_factors[19];
    RefClosureFactor actual_factors[19];
    OspreyVarPayload source;
    OspreyVarPayload prefix;
    OspreyVarPayload fold;
    OspreyVarPayload folded;
    OspreyVarPayload source_prefix;
    OspreyVarPayload folded_prefix;
    OspreyVarPayload source_field;
    OspreyVarPayload folded_field;
    OspreyKey source_key;
    OspreyKey prefix_key;
    OspreyKey fold_key;
    OspreyKey folded_key;
    OspreyKey source_prefix_key;
    OspreyKey folded_prefix_key;
    OspreyKey source_field_key;
    OspreyKey folded_field_key;
    uint32_t expected_var_count = 0;
    uint32_t expected_factor_count = 0;
    int64_t folded_offset = 0;
    bool eligible;

    if (ctx == NULL || ctx->graph == NULL || description == NULL ||
        ctx->graph->vars == NULL || ctx->graph->factors == NULL) return false;
    eligible = stage5_bp_reference_closure_eligible(description,
                                                    &folded_offset);
    memset(&source, 0, sizeof(source));
    source.chunk.address.region = description->region;
    source.chunk.address.offset = description->source_offset;
    source.chunk.size = description->width;
    memset(&prefix, 0, sizeof(prefix));
    prefix.heap_fold.region = description->region;
    prefix.heap_fold.size = description->prefix_size;
    memset(&fold, 0, sizeof(fold));
    fold.heap_fold.region = description->region;
    fold.heap_fold.size = description->fold_size;
    source_key = ref_var_key(OSPREY_PRED_PRIMITIVE_VAR, &source);
    prefix_key = ref_var_key(OSPREY_PRED_UNFOLDABLE_HEAP, &prefix);
    fold_key = ref_var_key(OSPREY_PRED_FOLDABLE_HEAP, &fold);
    ref_closure_var_add(expected_vars, &expected_var_count,
                        OSPREY_PRED_PRIMITIVE_VAR, &source, 0, 0.0,
                        OSPREY_RULE_NONE);
    ref_closure_var_add(expected_vars, &expected_var_count,
                        OSPREY_PRED_UNFOLDABLE_HEAP, &prefix, 0, 0.0,
                        OSPREY_RULE_NONE);
    ref_closure_var_add(expected_vars, &expected_var_count,
                        OSPREY_PRED_FOLDABLE_HEAP, &fold, 0, 0.0,
                        OSPREY_RULE_NONE);
    ref_closure_factor_add(expected_factors, &expected_factor_count,
                           OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                           OSPREY_POTENTIAL_PRIOR, false,
                           description->primitive_probability, 0,
                           &source_key, 1);
    ref_closure_factor_add(expected_factors, &expected_factor_count,
                           OSPREY_RULE_CC01, OSPREY_GRAPH_SECONDARY,
                           OSPREY_POTENTIAL_PRIOR, false,
                           description->prefix_probability, 0,
                           &prefix_key, 1);
    ref_closure_factor_add(expected_factors, &expected_factor_count,
                           OSPREY_RULE_CC02, OSPREY_GRAPH_SECONDARY,
                           OSPREY_POTENTIAL_PRIOR, false,
                           description->fold_probability, 0,
                           &fold_key, 1);
    if (eligible) {
        int64_t source_end;
        int64_t folded_end;
        OspreyKey positive[4];
        OspreyKey negative[3];
        OspreyKey implication[2];
        OspreyKey prefixes[3];

        if (!ref_closure_add_i64(description->source_offset,
                                 (int64_t)description->width, &source_end) ||
            !ref_closure_add_i64(folded_offset,
                                 (int64_t)description->width, &folded_end)) {
            return false;
        }
        folded = source;
        folded.chunk.address.offset = folded_offset;
        memset(&source_prefix, 0, sizeof(source_prefix));
        source_prefix.heap_fold.region = description->region;
        source_prefix.heap_fold.size = (uint64_t)source_end;
        memset(&folded_prefix, 0, sizeof(folded_prefix));
        folded_prefix.heap_fold.region = description->region;
        folded_prefix.heap_fold.size = (uint64_t)folded_end;
        memset(&source_field, 0, sizeof(source_field));
        source_field.attached.chunk = source.chunk;
        source_field.attached.base.region = description->region;
        memset(&folded_field, 0, sizeof(folded_field));
        folded_field.attached.chunk = folded.chunk;
        folded_field.attached.base.region = description->region;
        folded_key = ref_var_key(OSPREY_PRED_PRIMITIVE_VAR, &folded);
        source_prefix_key = ref_var_key(OSPREY_PRED_UNFOLDABLE_HEAP,
                                        &source_prefix);
        folded_prefix_key = ref_var_key(OSPREY_PRED_UNFOLDABLE_HEAP,
                                        &folded_prefix);
        source_field_key = ref_var_key(OSPREY_PRED_FIELD_OF, &source_field);
        folded_field_key = ref_var_key(OSPREY_PRED_FIELD_OF, &folded_field);
        if (description->folded_preexisting) {
            ref_closure_factor_add(expected_factors, &expected_factor_count,
                                   OSPREY_RULE_CB01,
                                   OSPREY_GRAPH_SECONDARY,
                                   OSPREY_POTENTIAL_PRIOR, false, 0.5, 0,
                                   &folded_key, 1);
        }
        ref_closure_var_add(expected_vars, &expected_var_count,
                            OSPREY_PRED_PRIMITIVE_VAR, &folded,
                            description->folded_preexisting ? 0 : 1,
                            description->folded_preexisting ? 0.0 : 0.8,
                            description->folded_preexisting
                                ? OSPREY_RULE_NONE : OSPREY_RULE_CC07);
        ref_closure_var_add(expected_vars, &expected_var_count,
                            OSPREY_PRED_UNFOLDABLE_HEAP, &source_prefix, 0,
                            0.8, OSPREY_RULE_CC03);
        ref_closure_var_add(expected_vars, &expected_var_count,
                            OSPREY_PRED_UNFOLDABLE_HEAP, &folded_prefix,
                            description->folded_preexisting ? 0 : 1,
                            0.8, OSPREY_RULE_CC03);
        ref_closure_var_add(expected_vars, &expected_var_count,
                            OSPREY_PRED_FIELD_OF, &source_field, 0, 0.8,
                            OSPREY_RULE_CD07);
        ref_closure_var_add(expected_vars, &expected_var_count,
                            OSPREY_PRED_FIELD_OF, &folded_field,
                            description->folded_preexisting ? 0 : 1,
                            0.8, OSPREY_RULE_CD07);
        positive[0] = source_key;
        positive[1] = prefix_key;
        positive[2] = fold_key;
        positive[3] = folded_key;
        ref_closure_factor_add(expected_factors, &expected_factor_count,
                               OSPREY_RULE_CC07, OSPREY_GRAPH_SECONDARY,
                               OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 3,
                               positive, 4);
        negative[0] = prefix_key;
        negative[1] = fold_key;
        negative[2] = source_key;
        ref_closure_factor_add(expected_factors, &expected_factor_count,
                               OSPREY_RULE_CC07, OSPREY_GRAPH_SECONDARY,
                               OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 2,
                               negative, 3);
        implication[0] = source_key;
        implication[1] = source_prefix_key;
        ref_closure_factor_add(expected_factors, &expected_factor_count,
                               OSPREY_RULE_CC03, OSPREY_GRAPH_SECONDARY,
                               OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                               implication, 2);
        implication[0] = folded_key;
        implication[1] = folded_prefix_key;
        ref_closure_factor_add(expected_factors, &expected_factor_count,
                               OSPREY_RULE_CC03, OSPREY_GRAPH_SECONDARY,
                               OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                               implication, 2);
        implication[0] = source_key;
        implication[1] = source_field_key;
        ref_closure_factor_add(expected_factors, &expected_factor_count,
                               OSPREY_RULE_CD07, OSPREY_GRAPH_SECONDARY,
                               OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                               implication, 2);
        implication[0] = folded_key;
        implication[1] = folded_field_key;
        ref_closure_factor_add(expected_factors, &expected_factor_count,
                               OSPREY_RULE_CD07, OSPREY_GRAPH_SECONDARY,
                               OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                               implication, 2);
        prefixes[0] = prefix_key;
        prefixes[1] = folded_prefix_key;
        prefixes[2] = source_prefix_key;
        for (uint32_t i = 0; i < 3; i++) {
            for (uint32_t j = i + 1; j < 3; j++) {
                OspreyKey pair[2] = { prefixes[i], prefixes[j] };
                ref_closure_factor_add(
                    expected_factors, &expected_factor_count,
                    OSPREY_RULE_CC04, OSPREY_GRAPH_SECONDARY,
                    OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1, pair, 2);
                pair[0] = prefixes[j];
                pair[1] = prefixes[i];
                ref_closure_factor_add(
                    expected_factors, &expected_factor_count,
                    OSPREY_RULE_CC04, OSPREY_GRAPH_SECONDARY,
                    OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1, pair, 2);
                pair[0] = prefixes[i];
                pair[1] = prefixes[j];
                ref_closure_factor_add(
                    expected_factors, &expected_factor_count,
                    OSPREY_RULE_CC05, OSPREY_GRAPH_SECONDARY,
                    OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1, pair, 2);
            }
        }
    }
    if (ctx->graph->vars->len != expected_var_count ||
        ctx->graph->factors->len != expected_factor_count) return false;
    qsort(expected_vars, expected_var_count, sizeof(expected_vars[0]),
          ref_closure_var_compare);
    for (uint32_t i = 0; i < expected_var_count; i++) {
        const OspreyVar *matched = NULL;
        for (guint j = 0; j < ctx->graph->vars->len; j++) {
            const OspreyVar *candidate = &g_array_index(
                ctx->graph->vars, OspreyVar, j);
            OspreyKey key = ref_var_key(candidate->kind,
                                        &candidate->payload);
            if (ref_key_equal(&key, &expected_vars[i].key)) {
                matched = candidate;
                break;
            }
        }
        if (matched == NULL ||
            !ref_closure_var_matches(matched, &expected_vars[i])) return false;
    }
    for (uint32_t i = 0; i < expected_factor_count; i++) {
        const OspreyFactor *factor = g_array_index(
            ctx->graph->factors, OspreyFactor *, i);
        if (!ref_closure_factor_from_actual(ctx, factor,
                                            &actual_factors[i])) return false;
    }
    qsort(expected_factors, expected_factor_count,
          sizeof(expected_factors[0]), ref_closure_factor_compare);
    qsort(actual_factors, expected_factor_count,
          sizeof(actual_factors[0]), ref_closure_factor_compare);
    for (uint32_t i = 0; i < expected_factor_count; i++) {
        if (ref_closure_factor_compare(&expected_factors[i],
                                       &actual_factors[i]) != 0) return false;
    }
    return true;
}
