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
