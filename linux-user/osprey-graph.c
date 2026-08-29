/*
 * OSPREY Stage 3.2 graph foundation.
 *
 * This file owns predicate identity/interning, deterministic candidate
 * proposal selection, factor validation/insertion, generic potentials, and
 * the canonical graph dump.  Rule-specific scans remain in osprey-rules.c.
 */

#include "osprey.h"
#include "osprey-internal.h"

#include <inttypes.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <string.h>

/* Diagnostic sink (snapshot.c). */
void log_msg(const char *fmt, ...);

/* ------------------------------------------------------------------ */
/* Canonical comparisons and key construction                         */
/* ------------------------------------------------------------------ */

static int cmp_u64(uint64_t a, uint64_t b)
{
    return a < b ? -1 : a != b;
}

static int cmp_i64(int64_t a, int64_t b)
{
    return a < b ? -1 : a != b;
}

static bool region_valid(const OspreyRegionId *region)
{
    return region != NULL && region->kind >= OSPREY_REGION_GLOBAL &&
           region->kind <= OSPREY_REGION_STACK_FUNCTION;
}

static bool address_valid(const OspreyAddress *address)
{
    return address != NULL && region_valid(&address->region);
}

static bool chunk_identity_valid(const OspreyChunk *chunk)
{
    return chunk != NULL && address_valid(&chunk->address) &&
           chunk->size != 0;
}

static int region_compare(const OspreyRegionId *a, const OspreyRegionId *b)
{
    int c = cmp_u64((uint64_t)a->kind, (uint64_t)b->kind);
    if (c != 0) return c;
    c = cmp_u64(a->code_image_id, b->code_image_id);
    if (c != 0) return c;
    return cmp_u64(a->site_offset, b->site_offset);
}

static int address_compare(const OspreyAddress *a, const OspreyAddress *b)
{
    int c = region_compare(&a->region, &b->region);
    if (c != 0) return c;
    return cmp_i64(a->offset, b->offset);
}

static int chunk_compare(const OspreyChunk *a, const OspreyChunk *b)
{
    int c = address_compare(&a->address, &b->address);
    return c != 0 ? c : cmp_u64(a->size, b->size);
}

int osprey_var_payload_compare(uint8_t kind, const OspreyVarPayload *a,
                               const OspreyVarPayload *b)
{
    int c;

    switch (kind) {
    case OSPREY_PRED_PRIMITIVE_VAR:
    case OSPREY_PRED_SCALAR:
        return chunk_compare(&a->chunk, &b->chunk);
    case OSPREY_PRED_PRIMITIVE_ACCESS:
        c = cmp_u64(a->prim_access.insn_pc, b->prim_access.insn_pc);
        return c != 0 ? c : chunk_compare(&a->prim_access.chunk,
                                           &b->prim_access.chunk);
    case OSPREY_PRED_UNFOLDABLE_HEAP:
    case OSPREY_PRED_FOLDABLE_HEAP:
        c = region_compare(&a->heap_fold.region, &b->heap_fold.region);
        return c != 0 ? c : cmp_u64(a->heap_fold.size, b->heap_fold.size);
    case OSPREY_PRED_HOMO_SEGMENT:
    case OSPREY_PRED_ARRAY:
        c = address_compare(&a->segment.a1, &b->segment.a1);
        if (c != 0) return c;
        c = address_compare(&a->segment.a2, &b->segment.a2);
        return c != 0 ? c : cmp_i64(a->segment.size, b->segment.size);
    case OSPREY_PRED_ARRAY_START:
        return address_compare(&a->addr, &b->addr);
    case OSPREY_PRED_FIELD_OF:
    case OSPREY_PRED_POINTER:
        c = chunk_compare(&a->attached.chunk, &b->attached.chunk);
        return c != 0 ? c : address_compare(&a->attached.base,
                                             &b->attached.base);
    default:
        return 0;
    }
}

static int key_compare(const OspreyKey *a, const OspreyKey *b)
{
    int c = cmp_u64(a->tag, b->tag);
    if (c != 0) return c;
    for (size_t i = 0; i < G_N_ELEMENTS(a->w); i++) {
        c = cmp_u64(a->w[i], b->w[i]);
        if (c != 0) return c;
    }
    return 0;
}

static void key_put_region(OspreyKey *key, const OspreyRegionId *region,
                           size_t word)
{
    key->w[word + 0] = (uint64_t)region->kind;
    key->w[word + 1] = region->code_image_id;
    key->w[word + 2] = region->site_offset;
}

static void key_put_address(OspreyKey *key, const OspreyAddress *address,
                            size_t word)
{
    key_put_region(key, &address->region, word);
    key->w[word + 3] = (uint64_t)address->offset;
}

static void key_put_chunk(OspreyKey *key, const OspreyChunk *chunk,
                          size_t word)
{
    key_put_address(key, &chunk->address, word);
    key->w[word + 4] = chunk->size;
}

/* Full predicate key.  The returned key is canonical for symmetric
 * HomoSegment endpoints. */
OspreyKey osprey_var_key(uint8_t kind, const OspreyVarPayload *payload)
{
    OspreyKey key;
    OspreyVarPayload canonical;

    memset(&key, 0, sizeof(key));
    memset(&canonical, 0, sizeof(canonical));
    key.tag = 0x564152ULL; /* VAR */
    key.w[0] = kind;
    if (payload == NULL) return key;

    switch (kind) {
    case OSPREY_PRED_PRIMITIVE_VAR:
    case OSPREY_PRED_SCALAR:
        canonical.chunk = payload->chunk;
        key_put_chunk(&key, &canonical.chunk, 1);
        break;
    case OSPREY_PRED_PRIMITIVE_ACCESS:
        canonical.prim_access = payload->prim_access;
        key_put_chunk(&key, &canonical.prim_access.chunk, 1);
        key.w[6] = canonical.prim_access.insn_pc;
        break;
    case OSPREY_PRED_UNFOLDABLE_HEAP:
    case OSPREY_PRED_FOLDABLE_HEAP:
        canonical.heap_fold = payload->heap_fold;
        key_put_region(&key, &canonical.heap_fold.region, 1);
        key.w[4] = canonical.heap_fold.size;
        break;
    case OSPREY_PRED_HOMO_SEGMENT: {
        OspreyAddress a1 = payload->segment.a1;
        OspreyAddress a2 = payload->segment.a2;
        if (address_compare(&a2, &a1) < 0) {
            OspreyAddress tmp = a1;
            a1 = a2;
            a2 = tmp;
        }
        key_put_address(&key, &a1, 1);
        key_put_address(&key, &a2, 5);
        key.w[9] = (uint64_t)payload->segment.size;
        break;
    }
    case OSPREY_PRED_ARRAY:
        key_put_address(&key, &payload->segment.a1, 1);
        key_put_address(&key, &payload->segment.a2, 5);
        key.w[9] = (uint64_t)payload->segment.size;
        break;
    case OSPREY_PRED_ARRAY_START:
        key_put_address(&key, &payload->addr, 1);
        break;
    case OSPREY_PRED_FIELD_OF:
    case OSPREY_PRED_POINTER:
        key_put_chunk(&key, &payload->attached.chunk, 1);
        key_put_address(&key, &payload->attached.base, 6);
        break;
    default:
        break;
    }
    return key;
}

static bool canonicalize_payload(uint8_t kind, const OspreyVarPayload *in,
                                 OspreyVarPayload *out)
{
    if (in == NULL || out == NULL) return false;
    memset(out, 0, sizeof(*out));
    switch (kind) {
    case OSPREY_PRED_PRIMITIVE_VAR:
    case OSPREY_PRED_SCALAR:
        if (!chunk_identity_valid(&in->chunk)) return false;
        out->chunk = in->chunk;
        return true;
    case OSPREY_PRED_PRIMITIVE_ACCESS:
        if (!chunk_identity_valid(&in->prim_access.chunk)) return false;
        if (!region_valid(&in->prim_access.chunk.address.region)) return false;
        out->prim_access = in->prim_access;
        return true;
    case OSPREY_PRED_UNFOLDABLE_HEAP:
        if (in->heap_fold.region.kind != OSPREY_REGION_HEAP_SITE) return false;
        out->heap_fold = in->heap_fold;
        return true;
    case OSPREY_PRED_FOLDABLE_HEAP:
        if (in->heap_fold.region.kind != OSPREY_REGION_HEAP_SITE) return false;
        out->heap_fold = in->heap_fold;
        return true;
    case OSPREY_PRED_HOMO_SEGMENT:
        if (!address_valid(&in->segment.a1) ||
            !address_valid(&in->segment.a2) || in->segment.size <= 0) {
            return false;
        }
        out->segment = in->segment;
        if (address_compare(&out->segment.a2, &out->segment.a1) < 0) {
            OspreyAddress tmp = out->segment.a1;
            out->segment.a1 = out->segment.a2;
            out->segment.a2 = tmp;
        }
        return true;
    case OSPREY_PRED_ARRAY:
        if (!address_valid(&in->segment.a1) ||
            !address_valid(&in->segment.a2) ||
            in->segment.a1.region.kind != in->segment.a2.region.kind ||
            in->segment.a1.region.code_image_id !=
                in->segment.a2.region.code_image_id ||
            in->segment.a1.region.site_offset !=
                in->segment.a2.region.site_offset ||
            in->segment.a1.offset >= in->segment.a2.offset ||
            in->segment.size <= 0) {
            return false;
        }
        int64_t span;
        if (!osprey_check_sub(in->segment.a2.offset,
                              in->segment.a1.offset, &span) ||
            span < in->segment.size) {
            return false;
        }
        out->segment = in->segment;
        return true;
    case OSPREY_PRED_ARRAY_START:
        if (!address_valid(&in->addr)) return false;
        out->addr = in->addr;
        return true;
    case OSPREY_PRED_FIELD_OF:
    case OSPREY_PRED_POINTER:
        if (!chunk_identity_valid(&in->attached.chunk) ||
            !address_valid(&in->attached.base)) return false;
        out->attached = in->attached;
        return true;
    default:
        return false;
    }
}

/* ------------------------------------------------------------------ */
/* Graph lifecycle                                                     */
/* ------------------------------------------------------------------ */

OspreyGraph *osprey_graph_new(void)
{
    OspreyGraph *graph = g_new0(OspreyGraph, 1);
    graph->vars = g_array_new(FALSE, FALSE, sizeof(OspreyVar));
    graph->var_index = g_hash_table_new_full(osprey_key_hash,
                                             osprey_key_equal,
                                             osprey_key_free, NULL);
    graph->hints = g_array_new(FALSE, FALSE, sizeof(OspreyHint));
    graph->factors = g_array_new(FALSE, FALSE, sizeof(OspreyFactor *));
    graph->factor_index = g_hash_table_new_full(osprey_factor_key_hash,
                                                osprey_factor_key_equal,
                                                g_free, NULL);
    graph->kind_region = g_hash_table_new_full(osprey_key_hash,
                                               osprey_key_equal,
                                               osprey_key_free, g_free);
    graph->extents = g_array_new(FALSE, FALSE, sizeof(OspreyRegionExtent));
    graph->construction_stage = OSPREY_GRAPH_BASE_CA;
    return graph;
}

void osprey_graph_free(OspreyGraph *graph)
{
    if (graph == NULL) return;
    if (graph->factors != NULL) {
        for (guint i = 0; i < graph->factors->len; i++) {
            OspreyFactor *factor = g_array_index(graph->factors,
                                                  OspreyFactor *, i);
            if (factor != NULL) {
                g_free(factor->var_ids);
                g_free(factor);
            }
        }
        g_array_free(graph->factors, TRUE);
    }
    if (graph->vars != NULL) g_array_free(graph->vars, TRUE);
    if (graph->var_index != NULL) g_hash_table_destroy(graph->var_index);
    if (graph->hints != NULL) g_array_free(graph->hints, TRUE);
    if (graph->factor_index != NULL) g_hash_table_destroy(graph->factor_index);
    if (graph->kind_region != NULL) g_hash_table_destroy(graph->kind_region);
    if (graph->extents != NULL) g_array_free(graph->extents, TRUE);
    g_free(graph->uf_parent);
    g_free(graph);
}

void osprey_graph_set_stage(OspreyGraph *graph, uint8_t stage)
{
    if (graph == NULL) return;
    graph->construction_stage = stage;
}

static void graph_set_error(OspreyContext *ctx, OspreyStatus status)
{
    if (ctx == NULL) return;
    if (ctx->last_status == OSPREY_OK || ctx->last_status == OSPREY_DISABLED) {
        ctx->last_status = status;
    }
}

/* ------------------------------------------------------------------ */
/* Predicate interning                                                  */
/* ------------------------------------------------------------------ */

OspreyInternResult osprey_intern_var(OspreyContext *ctx, uint8_t kind,
                                     const OspreyVarPayload *payload)
{
    OspreyInternResult result = { UINT32_MAX, false };
    OspreyVarPayload canonical;
    OspreyKey key;
    OspreyGraph *graph;
    gpointer existing;

    if (ctx == NULL || ctx->graph == NULL ||
        !canonicalize_payload(kind, payload, &canonical)) {
        graph_set_error(ctx, OSPREY_INVALID_GRAPH);
        return result;
    }
    graph = ctx->graph;
    key = osprey_var_key(kind, &canonical);
    existing = g_hash_table_lookup(graph->var_index, &key);
    if (existing != NULL) {
        result.id = (uint32_t)(uintptr_t)existing - 1;
        return result;
    }
    if (graph->vars->len >= ctx->config.max_variables ||
        graph->vars->len >= UINT32_MAX) {
        graph_set_error(ctx, OSPREY_LIMIT_EXCEEDED);
        return result;
    }

    OspreyVar variable;
    memset(&variable, 0, sizeof(variable));
    variable.id = graph->vars->len;
    variable.kind = kind;
    /* belief_valid is authoritative; keep the numeric payload ignored until
     * Stage 4 publishes an exact seed. */
    variable.belief = 0.0;
    variable.belief_valid = 0;
    variable.payload = canonical;
    g_array_append_val(graph->vars, variable);

    g_hash_table_insert(graph->var_index, osprey_key_new(&key),
                        GSIZE_TO_POINTER((gsize)variable.id + 1));
    if (graph->uf_size <= variable.id) {
        uint32_t new_size = variable.id + 1;
        graph->uf_parent = g_realloc(graph->uf_parent,
                                     (size_t)new_size * sizeof(uint32_t));
        for (uint32_t i = graph->uf_size; i < new_size; i++) {
            graph->uf_parent[i] = i;
        }
        graph->uf_size = new_size;
    }
    result.id = variable.id;
    result.inserted = true;
    return result;
}

static void graph_sync_union_find(OspreyGraph *graph)
{
    if (graph == NULL || graph->vars == NULL ||
        graph->uf_size >= graph->vars->len) return;
    uint64_t variable_count = graph->vars->len;
    uint32_t new_size = variable_count > UINT32_MAX
        ? UINT32_MAX : (uint32_t)variable_count;
    graph->uf_parent = g_realloc(graph->uf_parent,
                                 (size_t)new_size * sizeof(uint32_t));
    for (uint32_t i = graph->uf_size; i < new_size; i++) {
        graph->uf_parent[i] = i;
    }
    graph->uf_size = new_size;
}

static uint32_t uf_find(OspreyGraph *graph, uint32_t value)
{
    while (graph->uf_parent[value] != value) {
        graph->uf_parent[value] = graph->uf_parent[graph->uf_parent[value]];
        value = graph->uf_parent[value];
    }
    return value;
}

static void uf_union(OspreyGraph *graph, uint32_t a, uint32_t b)
{
    uint32_t ra = uf_find(graph, a);
    uint32_t rb = uf_find(graph, b);
    if (ra != rb) graph->uf_parent[ra] = rb;
}

uint32_t osprey_graph_component_count(const OspreyGraph *graph)
{
    if (graph == NULL || graph->vars == NULL) return 0;
    GHashTable *roots = g_hash_table_new(g_direct_hash, g_direct_equal);
    uint32_t count = 0;
    uint32_t synced = graph->uf_size < graph->vars->len
        ? graph->uf_size : graph->vars->len;
    for (uint32_t i = 0; i < synced; i++) {
        uint32_t root = i;
        while (graph->uf_parent[root] != root) root = graph->uf_parent[root];
        if (g_hash_table_lookup(roots, GSIZE_TO_POINTER(root)) == NULL) {
            g_hash_table_insert(roots, GSIZE_TO_POINTER(root),
                                GSIZE_TO_POINTER(1));
            count++;
        }
    }
    uint64_t missing = (uint64_t)graph->vars->len - synced;
    if (missing > UINT32_MAX - count) count = UINT32_MAX;
    else count += (uint32_t)missing;
    g_hash_table_destroy(roots);
    return count;
}

/* ------------------------------------------------------------------ */
/* Factors                                                             */
/* ------------------------------------------------------------------ */

guint osprey_factor_key_hash(gconstpointer data)
{
    const OspreyFactorKey *key = data;
    uint64_t hash = key->rule;
    hash ^= (uint64_t)key->stage << 8;
    hash ^= (uint64_t)key->potential_kind << 16;
    hash ^= (uint64_t)key->negative << 24;
    hash ^= (uint64_t)key->head_idx << 32;
    hash ^= (uint64_t)key->num_vars << 48;
    hash ^= key->p_bits + 0x9e3779b97f4a7c15ULL + (hash << 6) + (hash >> 2);
    if (key->num_vars > OSPREY_FACTOR_MAX_ARITY) {
        return (guint)hash;
    }
    for (uint32_t i = 0; i < key->num_vars; i++) {
        hash ^= (uint64_t)key->var_ids[i] + 0x9e3779b97f4a7c15ULL +
                (hash << 6) + (hash >> 2);
    }
    return (guint)hash;
}

gboolean osprey_factor_key_equal(gconstpointer a, gconstpointer b)
{
    const OspreyFactorKey *x = a;
    const OspreyFactorKey *y = b;
    if (x->rule != y->rule || x->stage != y->stage ||
        x->potential_kind != y->potential_kind ||
        x->negative != y->negative || x->head_idx != y->head_idx ||
        x->p_bits != y->p_bits || x->num_vars != y->num_vars ||
        x->num_vars > OSPREY_FACTOR_MAX_ARITY) {
        return FALSE;
    }
    for (uint32_t i = 0; i < x->num_vars; i++) {
        if (x->var_ids[i] != y->var_ids[i]) return FALSE;
    }
    return TRUE;
}

static bool rule_code_valid(uint16_t rule)
{
    return rule > OSPREY_RULE_NONE && rule < OSPREY_RULE_COUNT;
}

static OspreyFactorResult factor_error(OspreyContext *ctx, OspreyStatus status)
{
    OspreyFactorResult result = { status, UINT32_MAX, false };
    graph_set_error(ctx, status);
    return result;
}

static OspreyFactorResult factor_add_typed(OspreyContext *ctx, uint16_t rule,
                                           uint8_t stage,
                                           uint8_t potential_kind,
                                           uint16_t head_idx, bool negative,
                                           double probability,
                                           const uint32_t *var_ids,
                                           uint32_t num_vars)
{
    OspreyFactorResult result = { OSPREY_OK, UINT32_MAX, false };
    OspreyGraph *graph;
    OspreyFactorKey key;

    if (ctx == NULL || ctx->graph == NULL) {
        return factor_error(ctx, OSPREY_INVALID_GRAPH);
    }
    graph = ctx->graph;
    if (!rule_code_valid(rule) ||
        (stage != OSPREY_GRAPH_BASE_CA && stage != OSPREY_GRAPH_SECONDARY) ||
        (potential_kind != OSPREY_POTENTIAL_IMPLICATION &&
         potential_kind != OSPREY_POTENTIAL_PRIOR &&
         potential_kind != OSPREY_POTENTIAL_HARD_FALSE) ||
        num_vars == 0 || num_vars > OSPREY_FACTOR_MAX_ARITY ||
        var_ids == NULL || !isfinite(probability) || probability < 0.0 ||
        probability > 1.0) {
        return factor_error(ctx, OSPREY_INVALID_GRAPH);
    }

    switch (potential_kind) {
    case OSPREY_POTENTIAL_PRIOR:
        if (num_vars != 1 || head_idx != 0) {
            return factor_error(ctx, OSPREY_INVALID_GRAPH);
        }
        break;
    case OSPREY_POTENTIAL_IMPLICATION:
        if (num_vars < 2 || head_idx >= num_vars) {
            return factor_error(ctx, OSPREY_INVALID_GRAPH);
        }
        break;
    case OSPREY_POTENTIAL_HARD_FALSE:
        if (rule != OSPREY_RULE_CB06 ||
            stage != OSPREY_GRAPH_SECONDARY || num_vars != 1 ||
            head_idx != UINT16_MAX || negative || probability != 0.0) {
            return factor_error(ctx, OSPREY_INVALID_GRAPH);
        }
        break;
    default:
        return factor_error(ctx, OSPREY_INVALID_GRAPH);
    }

    memset(&key, 0, sizeof(key));
    key.rule = rule;
    key.stage = stage;
    key.potential_kind = potential_kind;
    key.negative = negative ? 1 : 0;
    key.head_idx = head_idx;
    key.p_bits = 0;
    memcpy(&key.p_bits, &probability, sizeof(key.p_bits));
    key.num_vars = num_vars;
    for (uint32_t i = 0; i < num_vars; i++) {
        if (var_ids[i] >= graph->vars->len) {
            return factor_error(ctx, OSPREY_INVALID_GRAPH);
        }
        for (uint32_t j = 0; j < i; j++) {
            if (var_ids[j] == var_ids[i]) {
                return factor_error(ctx, OSPREY_INVALID_GRAPH);
            }
        }
        key.var_ids[i] = var_ids[i];
    }
    graph_sync_union_find(graph);

    gpointer existing = g_hash_table_lookup(graph->factor_index, &key);
    if (existing != NULL) {
        result.id = (uint32_t)(uintptr_t)existing - 1;
        return result;
    }
    if (graph->factors->len >= ctx->config.max_factors ||
        graph->factors->len >= UINT32_MAX) {
        return factor_error(ctx, OSPREY_LIMIT_EXCEEDED);
    }

    OspreyFactor *factor = g_new0(OspreyFactor, 1);
    factor->id = graph->factors->len;
    factor->rule = rule;
    factor->head_idx = head_idx;
    factor->negative = negative ? 1 : 0;
    factor->stage = stage;
    factor->potential_kind = potential_kind;
    factor->p = probability;
    factor->num_vars = num_vars;
    factor->var_ids = g_new(uint32_t, num_vars);
    memcpy(factor->var_ids, var_ids, (size_t)num_vars * sizeof(uint32_t));
    g_array_append_val(graph->factors, factor);
    OspreyFactorKey *stored_key = g_new(OspreyFactorKey, 1);
    *stored_key = key;
    g_hash_table_insert(graph->factor_index, stored_key,
                        GSIZE_TO_POINTER((gsize)factor->id + 1));
    for (uint32_t i = 1; i < num_vars; i++) {
        uf_union(graph, var_ids[0], var_ids[i]);
    }
    result.id = factor->id;
    result.inserted = true;
    return result;
}

OspreyFactorResult osprey_factor_add_ex(OspreyContext *ctx, uint16_t rule,
                                        uint8_t stage, uint8_t potential_kind,
                                        uint16_t head_idx, bool negative,
                                        double probability,
                                        const uint32_t *var_ids,
                                        uint32_t num_vars)
{
    return factor_add_typed(ctx, rule, stage, potential_kind, head_idx,
                            negative, probability, var_ids, num_vars);
}

OspreyFactorResult osprey_factor_add_prior(OspreyContext *ctx, uint16_t rule,
                                           uint8_t stage, bool negative,
                                           double probability,
                                           uint32_t head_id)
{
    return factor_add_typed(ctx, rule, stage, OSPREY_POTENTIAL_PRIOR, 0,
                            negative, probability, &head_id, 1);
}

OspreyFactorResult osprey_factor_add_implication(
    OspreyContext *ctx, uint16_t rule, uint8_t stage, bool negative,
    double probability, const uint32_t *antecedent_ids,
    uint32_t num_antecedents, uint32_t head_id)
{
    uint32_t ids[OSPREY_FACTOR_MAX_ARITY];

    if (num_antecedents == 0 ||
        num_antecedents >= OSPREY_FACTOR_MAX_ARITY ||
        antecedent_ids == NULL) {
        return factor_error(ctx, OSPREY_INVALID_GRAPH);
    }
    memcpy(ids, antecedent_ids,
           (size_t)num_antecedents * sizeof(antecedent_ids[0]));
    ids[num_antecedents] = head_id;
    return factor_add_typed(ctx, rule, stage, OSPREY_POTENTIAL_IMPLICATION,
                            num_antecedents, negative, probability, ids,
                            num_antecedents + 1);
}

OspreyFactorResult osprey_factor_add_hard_false(OspreyContext *ctx,
                                                uint16_t rule, uint8_t stage,
                                                uint32_t var_id)
{
    return factor_add_typed(ctx, rule, stage, OSPREY_POTENTIAL_HARD_FALSE,
                            UINT16_MAX, false, 0.0, &var_id, 1);
}

static void factor_batch_record(OspreyFactorBatchResult *batch,
                                OspreyFactorResult result)
{
    if (result.status != OSPREY_OK) {
        batch->status = result.status;
    } else if (result.inserted && batch->inserted != UINT32_MAX) {
        batch->inserted++;
    }
}

OspreyFactorBatchResult osprey_factor_add_bidirectional(
    OspreyContext *ctx, uint16_t rule, uint8_t stage, bool negative,
    double probability, uint32_t left_id, uint32_t right_id)
{
    OspreyFactorBatchResult batch = { OSPREY_OK, 0 };
    OspreyFactorResult result = osprey_factor_add_implication(
        ctx, rule, stage, negative, probability, &left_id, 1, right_id);
    factor_batch_record(&batch, result);
    if (batch.status != OSPREY_OK) return batch;
    result = osprey_factor_add_implication(ctx, rule, stage, negative,
                                           probability, &right_id, 1,
                                           left_id);
    factor_batch_record(&batch, result);
    return batch;
}

OspreyFactorBatchResult osprey_factor_add_conjunction_bidirectional(
    OspreyContext *ctx, uint16_t rule, uint8_t stage, bool negative,
    double probability, const uint32_t *antecedent_ids,
    uint32_t num_antecedents, uint32_t head_id)
{
    OspreyFactorBatchResult batch = { OSPREY_OK, 0 };
    OspreyFactorResult result = osprey_factor_add_implication(
        ctx, rule, stage, negative, probability, antecedent_ids,
        num_antecedents, head_id);
    factor_batch_record(&batch, result);
    if (batch.status != OSPREY_OK) return batch;
    for (uint32_t i = 0; i < num_antecedents; i++) {
        result = osprey_factor_add_implication(ctx, rule, stage, negative,
                                               probability, &head_id, 1,
                                               antecedent_ids[i]);
        factor_batch_record(&batch, result);
        if (batch.status != OSPREY_OK) break;
    }
    return batch;
}

OspreyFactorBatchResult osprey_factor_add_multi_head(
    OspreyContext *ctx, uint16_t rule, uint8_t stage, bool negative,
    double probability, const uint32_t *antecedent_ids,
    uint32_t num_antecedents, const uint32_t *head_ids, uint32_t num_heads)
{
    OspreyFactorBatchResult batch = { OSPREY_OK, 0 };

    if (num_heads == 0 || num_heads > OSPREY_FACTOR_MAX_ARITY ||
        head_ids == NULL || num_antecedents >= OSPREY_FACTOR_MAX_ARITY ||
        (num_antecedents != 0 && antecedent_ids == NULL)) {
        batch.status = OSPREY_INVALID_GRAPH;
        graph_set_error(ctx, batch.status);
        return batch;
    }
    for (uint32_t i = 0; i < num_heads; i++) {
        OspreyFactorResult result = num_antecedents == 0
            ? osprey_factor_add_prior(ctx, rule, stage, negative,
                                      probability, head_ids[i])
            : osprey_factor_add_implication(
                  ctx, rule, stage, negative, probability, antecedent_ids,
                  num_antecedents, head_ids[i]);
        factor_batch_record(&batch, result);
        if (batch.status != OSPREY_OK) break;
    }
    return batch;
}

OspreyFactorResult osprey_factor_add(OspreyContext *ctx, uint16_t rule,
                                     uint16_t head_idx, bool negative,
                                     double probability,
                                     const uint32_t *var_ids,
                                     uint32_t num_vars)
{
    uint8_t stage = OSPREY_GRAPH_BASE_CA;
    if (ctx != NULL && ctx->graph != NULL) {
        if (ctx->graph->construction_stage == OSPREY_GRAPH_SECONDARY) {
            stage = OSPREY_GRAPH_SECONDARY;
        } else if (ctx->graph->construction_stage != OSPREY_GRAPH_BASE_CA) {
            return factor_error(ctx, OSPREY_INVALID_GRAPH);
        }
    }
    if (num_vars == 1) {
        /* Existing rule compilers pass either head 0 or UINT16_MAX for
         * unary priors.  The stored representation is always head 0. */
        if (head_idx != 0 && head_idx != UINT16_MAX) {
            return factor_error(ctx, OSPREY_INVALID_GRAPH);
        }
        head_idx = 0;
        return factor_add_typed(ctx, rule, stage, OSPREY_POTENTIAL_PRIOR,
                                head_idx, negative, probability, var_ids,
                                num_vars);
    }
    return factor_add_typed(ctx, rule, stage, OSPREY_POTENTIAL_IMPLICATION,
                            head_idx, negative, probability, var_ids,
                            num_vars);
}

/* Pure generic factor potential.  `assignment` has one byte per semantic
 * variable, with zero/one as the only accepted values. */
bool osprey_factor_log_weight(const OspreyFactor *factor,
                              const uint8_t *assignment,
                              double *log_weight)
{
    double weight;
    bool all_antecedents;

    if (factor == NULL || assignment == NULL || log_weight == NULL ||
        factor->num_vars == 0 || factor->num_vars > OSPREY_FACTOR_MAX_ARITY ||
        factor->negative > 1 || !rule_code_valid(factor->rule) ||
        (factor->stage != OSPREY_GRAPH_BASE_CA &&
         factor->stage != OSPREY_GRAPH_SECONDARY) ||
        !isfinite(factor->p) || factor->p < 0.0 || factor->p > 1.0) {
        return false;
    }
    for (uint32_t i = 0; i < factor->num_vars; i++) {
        if (assignment[i] > 1) return false;
    }
    switch (factor->potential_kind) {
    case OSPREY_POTENTIAL_PRIOR:
        if (factor->num_vars != 1 || factor->head_idx != 0) return false;
        weight = assignment[0] ? factor->p : 1.0 - factor->p;
        break;
    case OSPREY_POTENTIAL_IMPLICATION:
        if (factor->num_vars < 2 || factor->head_idx >= factor->num_vars) {
            return false;
        }
        all_antecedents = true;
        for (uint32_t i = 0; i < factor->num_vars; i++) {
            if (i != factor->head_idx && assignment[i] == 0) {
                all_antecedents = false;
                break;
            }
        }
        if (all_antecedents) {
            weight = assignment[factor->head_idx] ? factor->p :
                                                     1.0 - factor->p;
        } else {
            weight = factor->p > 1.0 - factor->p ? factor->p :
                                                     1.0 - factor->p;
        }
        break;
    case OSPREY_POTENTIAL_HARD_FALSE:
        if (factor->rule != OSPREY_RULE_CB06 ||
            factor->stage != OSPREY_GRAPH_SECONDARY ||
            factor->num_vars != 1 || factor->head_idx != UINT16_MAX ||
            factor->negative != 0 || factor->p != 0.0) {
            return false;
        }
        weight = assignment[0] ? 0.0 : 1.0;
        break;
    default:
        return false;
    }
    if (weight == 0.0) {
        *log_weight = -INFINITY;
    } else {
        *log_weight = log(weight);
    }
    return true;
}

/* ------------------------------------------------------------------ */
/* Candidate extents and deterministic proposal selection              */
/* ------------------------------------------------------------------ */

typedef struct CandidateEntry {
    OspreyKey key;
    OspreyCandidateProposal proposal;
    OspreyRegionId primary_region;
    uint64_t source_rule_bits;
} CandidateEntry;

typedef struct CandidateBucketDelta {
    OspreyRegionId region;
    uint8_t kind;
    uint64_t kept;
    uint64_t dropped;
} CandidateBucketDelta;

static int extent_compare(gconstpointer ap, gconstpointer bp)
{
    const OspreyRegionExtent *a = ap;
    const OspreyRegionExtent *b = bp;
    int c = region_compare(&a->region, &b->region);
    if (c != 0) return c;
    c = cmp_i64(a->lo, b->lo);
    if (c != 0) return c;
    return cmp_i64(a->hi, b->hi);
}

static bool extent_add(OspreyGraph *graph, const OspreyRegionId *region,
                       int64_t lo, int64_t hi)
{
    if (!region_valid(region) || lo > hi) return false;
    for (guint i = 0; i < graph->extents->len; i++) {
        OspreyRegionExtent *extent = &g_array_index(graph->extents,
                                                    OspreyRegionExtent, i);
        if (region_compare(&extent->region, region) != 0) continue;
        if (lo < extent->lo) extent->lo = lo;
        if (hi > extent->hi) extent->hi = hi;
        return true;
    }
    OspreyRegionExtent extent;
    memset(&extent, 0, sizeof(extent));
    extent.region = *region;
    extent.lo = lo;
    extent.hi = hi;
    g_array_append_val(graph->extents, extent);
    return true;
}

static bool signed_size_end(int64_t offset, uint64_t size, int64_t *end)
{
    if (size > (uint64_t)INT64_MAX) return false;
    return osprey_check_add(offset, (int64_t)size, end);
}

static bool extent_add_chunk(OspreyGraph *graph, const OspreyChunk *chunk)
{
    int64_t end;
    if (!chunk_identity_valid(chunk) ||
        !signed_size_end(chunk->address.offset, chunk->size, &end)) {
        return false;
    }
    return extent_add(graph, &chunk->address.region, chunk->address.offset,
                      end);
}

static bool extent_for(const OspreyGraph *graph, const OspreyRegionId *region,
                       int64_t *lo, int64_t *hi);
static bool extent_contains(const OspreyGraph *graph,
                            const OspreyRegionId *region,
                            int64_t lo, int64_t hi);

static bool raw_delta(uint64_t raw, uint64_t base, int64_t *out)
{
    uint64_t delta;
    if (raw >= base) {
        delta = raw - base;
        if (delta > (uint64_t)INT64_MAX) return false;
        *out = (int64_t)delta;
        return true;
    }
    delta = base - raw;
    if (delta > (uint64_t)INT64_MAX) return false;
    *out = -(int64_t)delta;
    return true;
}

static OspreyStatus region_instance_span(const OspreyRegionInstance *instance,
                                         int64_t *lo, int64_t *hi)
{
    if (instance == NULL || !region_valid(&instance->region) ||
        instance->raw_min > instance->raw_max) {
        return OSPREY_INVALID_GRAPH;
    }
    if (!raw_delta(instance->raw_min, instance->raw_base, lo) ||
        !raw_delta(instance->raw_max, instance->raw_base, hi)) {
        return OSPREY_GRAPH_ARITHMETIC;
    }
    return *lo <= *hi ? OSPREY_OK : OSPREY_INVALID_GRAPH;
}

static OspreyStatus extent_add_region_instance(
    OspreyGraph *graph, const OspreyRegionInstance *instance)
{
    int64_t lo, hi;
    OspreyStatus status = region_instance_span(instance, &lo, &hi);
    if (status != OSPREY_OK) return status;
    return extent_add(graph, &instance->region, lo, hi)
        ? OSPREY_OK : OSPREY_INVALID_GRAPH;
}

static OspreyStatus extent_add_nonheap_chunk(OspreyGraph *graph,
                                             const OspreyChunk *chunk)
{
    if (!chunk_identity_valid(chunk)) return OSPREY_INVALID_GRAPH;
    if (chunk->address.region.kind == OSPREY_REGION_HEAP_SITE) {
        return OSPREY_OK;
    }
    int64_t end;
    if (!signed_size_end(chunk->address.offset, chunk->size, &end)) {
        return OSPREY_GRAPH_ARITHMETIC;
    }
    return extent_add_chunk(graph, chunk)
        ? OSPREY_OK : OSPREY_INVALID_GRAPH;
}

static bool extent_catalog_contains_chunk(const OspreyGraph *graph,
                                          const OspreyChunk *chunk)
{
    int64_t end;
    if (!chunk_identity_valid(chunk) ||
        !signed_size_end(chunk->address.offset, chunk->size, &end)) {
        return false;
    }
    return extent_contains(graph, &chunk->address.region,
                           chunk->address.offset, end);
}

static bool f06_matches_alloc(const OspreyContext *ctx,
                              const OspreyRegionId *region,
                              uint64_t total)
{
    for (guint i = 0; i < ctx->alloc_facts->len; i++) {
        const OspreyMallocFact *fact = &g_array_index(ctx->alloc_facts,
                                                      OspreyMallocFact, i);
        if (fact->site_pc == region->site_offset &&
            fact->requested_size == total) return true;
    }
    return false;
}

static OspreyStatus extent_catalog_validate(const OspreyContext *ctx,
                                            const OspreyGraph *graph)
{
#define CHECK_HEAP_CHUNK(_chunk) \
    do { \
        if ((_chunk).address.region.kind == OSPREY_REGION_HEAP_SITE) { \
            int64_t chunk_end; \
            if (!chunk_identity_valid(&(_chunk))) { \
                return OSPREY_INVALID_GRAPH; \
            } \
            if (!signed_size_end((_chunk).address.offset, (_chunk).size, \
                                 &chunk_end)) { \
                return OSPREY_GRAPH_ARITHMETIC; \
            } \
            if (!extent_catalog_contains_chunk(graph, &(_chunk))) { \
                return OSPREY_INVALID_GRAPH; \
            } \
        } \
    } while (0)
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        const OspreyAccessFact *fact = &g_array_index(
            ctx->access_facts, OspreyAccessFact, i);
        CHECK_HEAP_CHUNK(fact->chunk);
    }
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        const OspreyBaseFact *fact = &g_array_index(ctx->base_facts,
                                                    OspreyBaseFact, i);
        CHECK_HEAP_CHUNK(fact->chunk);
    }
    for (guint i = 0; i < ctx->copy_facts->len; i++) {
        const OspreyCopyFact *fact = &g_array_index(ctx->copy_facts,
                                                    OspreyCopyFact, i);
        CHECK_HEAP_CHUNK(fact->source);
        CHECK_HEAP_CHUNK(fact->destination);
    }
    for (guint i = 0; i < ctx->points_facts->len; i++) {
        const OspreyPointsToFact *fact = &g_array_index(ctx->points_facts,
                                                        OspreyPointsToFact, i);
        CHECK_HEAP_CHUNK(fact->pointer_chunk);
    }
#undef CHECK_HEAP_CHUNK

    for (guint i = 0; i < ctx->region_instances->len; i++) {
        const OspreyRegionInstance *instance = &g_array_index(
            ctx->region_instances, OspreyRegionInstance, i);
        if (instance->region.kind != OSPREY_REGION_HEAP_SITE) continue;
        int64_t lo, hi;
        OspreyStatus status = region_instance_span(instance, &lo, &hi);
        if (status != OSPREY_OK) return status;
        if (!extent_contains(graph, &instance->region, lo, hi)) {
            return OSPREY_INVALID_GRAPH;
        }
    }

    for (guint i = 0; i < ctx->mayarray_facts->len; i++) {
        const OspreyMayArrayFact *fact = &g_array_index(
            ctx->mayarray_facts, OspreyMayArrayFact, i);
        uint64_t total;
        int64_t end;
        if (!address_valid(&fact->start) ||
            fact->evidence_kind != OSPREY_MAY_ARRAY_CALLOC_GEOMETRY ||
            fact->element_count == 0 || fact->element_size == 0) {
            return OSPREY_INVALID_GRAPH;
        }
        if (!osprey_check_mul(fact->element_count, fact->element_size,
                              &total) || total > (uint64_t)INT64_MAX ||
            !osprey_check_add(fact->start.offset, (int64_t)total, &end)) {
            return OSPREY_GRAPH_ARITHMETIC;
        }
        if (fact->start.region.kind == OSPREY_REGION_HEAP_SITE &&
            (!f06_matches_alloc(ctx, &fact->start.region, total) ||
             !extent_contains(graph, &fact->start.region,
                              fact->start.offset, end))) {
            return OSPREY_INVALID_GRAPH;
        }
    }
    return OSPREY_OK;
}

static OspreyStatus build_extent_catalog(OspreyContext *ctx)
{
    OspreyGraph *graph = ctx->graph;
    if (graph->extents_built) return OSPREY_OK;
    g_array_set_size(graph->extents, 0);

    /* Heap extents come only from successful F05 sizes.  Region instances
     * and ordinary F01-F04 chunks validate against that extent but cannot
     * enlarge it. */
    for (guint i = 0; i < ctx->region_instances->len; i++) {
        const OspreyRegionInstance *instance = &g_array_index(
            ctx->region_instances, OspreyRegionInstance, i);
        OspreyStatus status;
        if (instance->region.kind == OSPREY_REGION_HEAP_SITE) {
            int64_t instance_lo, instance_hi;
            status = region_instance_span(instance, &instance_lo,
                                          &instance_hi);
        } else {
            status = extent_add_region_instance(graph, instance);
        }
        if (status != OSPREY_OK) return status;
    }
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        const OspreyAccessFact *fact = &g_array_index(
            ctx->access_facts, OspreyAccessFact, i);
        OspreyStatus status = extent_add_nonheap_chunk(graph, &fact->chunk);
        if (status != OSPREY_OK) return status;
    }
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        const OspreyBaseFact *fact = &g_array_index(ctx->base_facts,
                                                    OspreyBaseFact, i);
        OspreyStatus status = extent_add_nonheap_chunk(graph, &fact->chunk);
        if (status != OSPREY_OK) return status;
    }
    for (guint i = 0; i < ctx->copy_facts->len; i++) {
        const OspreyCopyFact *fact = &g_array_index(ctx->copy_facts,
                                                    OspreyCopyFact, i);
        OspreyStatus status = extent_add_nonheap_chunk(graph, &fact->source);
        if (status != OSPREY_OK) return status;
        status = extent_add_nonheap_chunk(graph, &fact->destination);
        if (status != OSPREY_OK) return status;
    }
    for (guint i = 0; i < ctx->points_facts->len; i++) {
        const OspreyPointsToFact *fact = &g_array_index(ctx->points_facts,
                                                        OspreyPointsToFact, i);
        OspreyStatus status = extent_add_nonheap_chunk(
            graph, &fact->pointer_chunk);
        if (status != OSPREY_OK) return status;
    }
    for (guint i = 0; i < ctx->alloc_facts->len; i++) {
        const OspreyMallocFact *fact = &g_array_index(ctx->alloc_facts,
                                                      OspreyMallocFact, i);
        OspreyRegionId region;
        memset(&region, 0, sizeof(region));
        region.kind = OSPREY_REGION_HEAP_SITE;
        region.site_offset = fact->site_pc;
        if (fact->requested_size > (uint64_t)INT64_MAX) {
            return OSPREY_GRAPH_ARITHMETIC;
        }
        if (!extent_add(graph, &region, 0,
                        (int64_t)fact->requested_size)) {
            return OSPREY_INVALID_GRAPH;
        }
    }
    g_array_sort(graph->extents, extent_compare);
    OspreyStatus status = extent_catalog_validate(ctx, graph);
    if (status != OSPREY_OK) return status;
    graph->extents_built = true;
    return OSPREY_OK;
}

static bool extent_for(const OspreyGraph *graph, const OspreyRegionId *region,
                       int64_t *lo, int64_t *hi)
{
    for (guint i = 0; i < graph->extents->len; i++) {
        const OspreyRegionExtent *extent = &g_array_index(
            graph->extents, OspreyRegionExtent, i);
        if (region_compare(&extent->region, region) == 0) {
            *lo = extent->lo;
            *hi = extent->hi;
            return true;
        }
    }
    return false;
}

static bool extent_contains(const OspreyGraph *graph,
                            const OspreyRegionId *region,
                            int64_t lo, int64_t hi)
{
    int64_t extent_lo, extent_hi;
    return lo <= hi && extent_for(graph, region, &extent_lo, &extent_hi) &&
           lo >= extent_lo && hi <= extent_hi;
}

static bool extent_contains_point(const OspreyGraph *graph,
                                  const OspreyAddress *address)
{
    int64_t lo, hi;
    return extent_for(graph, &address->region, &lo, &hi) &&
           address->offset >= lo && address->offset <= hi;
}

static bool extent_contains_start(const OspreyGraph *graph,
                                  const OspreyAddress *address)
{
    int64_t lo, hi;
    return extent_for(graph, &address->region, &lo, &hi) &&
           address->offset >= lo && address->offset < hi;
}

static bool proposal_primary_region(uint8_t kind,
                                    const OspreyVarPayload *payload,
                                    OspreyRegionId *region)
{
    switch (kind) {
    case OSPREY_PRED_PRIMITIVE_VAR:
    case OSPREY_PRED_SCALAR:
    case OSPREY_PRED_PRIMITIVE_ACCESS:
    case OSPREY_PRED_FIELD_OF:
    case OSPREY_PRED_POINTER:
        *region = kind == OSPREY_PRED_PRIMITIVE_ACCESS
            ? payload->prim_access.chunk.address.region
            : kind == OSPREY_PRED_FIELD_OF || kind == OSPREY_PRED_POINTER
                ? payload->attached.chunk.address.region
                : payload->chunk.address.region;
        return true;
    case OSPREY_PRED_UNFOLDABLE_HEAP:
    case OSPREY_PRED_FOLDABLE_HEAP:
        *region = payload->heap_fold.region;
        return true;
    case OSPREY_PRED_HOMO_SEGMENT:
    case OSPREY_PRED_ARRAY:
        *region = payload->segment.a1.region;
        return true;
    case OSPREY_PRED_ARRAY_START:
        *region = payload->addr.region;
        return true;
    default:
        return false;
    }
}

static bool proposal_bounds_valid(OspreyContext *ctx, uint8_t kind,
                                  const OspreyVarPayload *payload)
{
    OspreyGraph *graph = ctx->graph;
    int64_t end;
    switch (kind) {
    case OSPREY_PRED_PRIMITIVE_VAR:
    case OSPREY_PRED_SCALAR:
        return signed_size_end(payload->chunk.address.offset,
                               payload->chunk.size, &end) &&
               extent_contains(graph, &payload->chunk.address.region,
                               payload->chunk.address.offset, end);
    case OSPREY_PRED_PRIMITIVE_ACCESS:
        return signed_size_end(payload->prim_access.chunk.address.offset,
                               payload->prim_access.chunk.size, &end) &&
               extent_contains(graph,
                               &payload->prim_access.chunk.address.region,
                               payload->prim_access.chunk.address.offset, end);
    case OSPREY_PRED_UNFOLDABLE_HEAP:
    case OSPREY_PRED_FOLDABLE_HEAP:
        return extent_contains(graph, &payload->heap_fold.region, 0,
                               payload->heap_fold.size > (uint64_t)INT64_MAX
                                   ? INT64_MAX
                                   : (int64_t)payload->heap_fold.size) &&
               payload->heap_fold.size <= (uint64_t)INT64_MAX;
    case OSPREY_PRED_HOMO_SEGMENT: {
        int64_t e1, e2;
        if (payload->segment.size <= 0 ||
            !osprey_check_add(payload->segment.a1.offset,
                              payload->segment.size, &e1) ||
            !osprey_check_add(payload->segment.a2.offset,
                              payload->segment.size, &e2)) return false;
        return extent_contains(graph, &payload->segment.a1.region,
                               payload->segment.a1.offset, e1) &&
               extent_contains(graph, &payload->segment.a2.region,
                               payload->segment.a2.offset, e2);
    }
    case OSPREY_PRED_ARRAY: {
        int64_t length;
        return payload->segment.size > 0 &&
               payload->segment.a1.offset < payload->segment.a2.offset &&
               osprey_check_sub(payload->segment.a2.offset,
                                payload->segment.a1.offset, &length) &&
               length >= payload->segment.size &&
               extent_contains(graph, &payload->segment.a1.region,
                               payload->segment.a1.offset,
                               payload->segment.a2.offset);
    }
    case OSPREY_PRED_ARRAY_START:
        return extent_contains_start(graph, &payload->addr);
    case OSPREY_PRED_FIELD_OF: {
        int64_t base_end;
        if (region_compare(&payload->attached.chunk.address.region,
                           &payload->attached.base.region) != 0 ||
            !signed_size_end(payload->attached.chunk.address.offset,
                             payload->attached.chunk.size, &end) ||
            !signed_size_end(payload->attached.base.offset,
                             payload->attached.chunk.size, &base_end) ||
            !extent_contains(graph, &payload->attached.chunk.address.region,
                             payload->attached.chunk.address.offset, end) ||
            !extent_contains(graph, &payload->attached.base.region,
                             payload->attached.base.offset, base_end)) {
            return false;
        }
        int64_t relative;
        if (!osprey_check_sub(payload->attached.chunk.address.offset,
                              payload->attached.base.offset, &relative) ||
            relative < 0) return false;
        return true;
    }
    case OSPREY_PRED_POINTER:
        return signed_size_end(payload->attached.chunk.address.offset,
                               payload->attached.chunk.size, &end) &&
               extent_contains(graph, &payload->attached.chunk.address.region,
                               payload->attached.chunk.address.offset, end) &&
               address_valid(&payload->attached.base) &&
               extent_contains_point(graph, &payload->attached.base);
    default:
        return false;
    }
}

static bool observed_chunk_start(const OspreyContext *ctx,
                                 const OspreyAddress *address)
{
#define CHECK_CHUNK_START(_chunk) \
    if (address_compare(&(_chunk).address, address) == 0) return true
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        const OspreyAccessFact *fact = &g_array_index(ctx->access_facts,
                                                      OspreyAccessFact, i);
        CHECK_CHUNK_START(fact->chunk);
    }
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        const OspreyBaseFact *fact = &g_array_index(ctx->base_facts,
                                                    OspreyBaseFact, i);
        CHECK_CHUNK_START(fact->chunk);
    }
    for (guint i = 0; i < ctx->copy_facts->len; i++) {
        const OspreyCopyFact *fact = &g_array_index(ctx->copy_facts,
                                                    OspreyCopyFact, i);
        CHECK_CHUNK_START(fact->source);
        CHECK_CHUNK_START(fact->destination);
    }
    for (guint i = 0; i < ctx->points_facts->len; i++) {
        const OspreyPointsToFact *fact = &g_array_index(ctx->points_facts,
                                                        OspreyPointsToFact, i);
        CHECK_CHUNK_START(fact->pointer_chunk);
    }
#undef CHECK_CHUNK_START
    return false;
}

static bool proposal_valid(OspreyContext *ctx, const OspreyCandidateProposal *p,
                           OspreyVarPayload *canonical,
                           OspreyRegionId *primary_region)
{
    if (p == NULL || !isfinite(p->prior) || p->prior < 0.0 ||
        p->prior > 1.0 || !rule_code_valid(p->source_rule) ||
        p->source_rule >= 64 ||
        !canonicalize_payload(p->predicate_kind, &p->payload, canonical) ||
        !proposal_primary_region(p->predicate_kind, canonical,
                                 primary_region) ||
        !proposal_bounds_valid(ctx, p->predicate_kind, canonical)) {
        return false;
    }
    if (p->predicate_kind == OSPREY_PRED_HOMO_SEGMENT &&
        (!observed_chunk_start(ctx, &canonical->segment.a1) ||
         !observed_chunk_start(ctx, &canonical->segment.a2))) {
        return false;
    }
    return true;
}

static int candidate_entry_compare(gconstpointer ap, gconstpointer bp)
{
    const CandidateEntry *a = ap;
    const CandidateEntry *b = bp;
    int c = cmp_u64(a->proposal.predicate_kind,
                    b->proposal.predicate_kind);
    if (c != 0) return c;
    c = region_compare(&a->primary_region, &b->primary_region);
    if (c != 0) return c;
    if (a->proposal.direct_support != b->proposal.direct_support) {
        return a->proposal.direct_support > b->proposal.direct_support ? -1 : 1;
    }
    if (a->proposal.prior != b->proposal.prior) {
        return a->proposal.prior > b->proposal.prior ? -1 : 1;
    }
    return osprey_var_payload_compare(a->proposal.predicate_kind,
                           &a->proposal.payload, &b->proposal.payload);
}

static void candidate_evidence_merge(OspreyGraph *graph, uint32_t var_id,
                                     const CandidateEntry *entry)
{
    OspreyVar *variable = &g_array_index(graph->vars, OspreyVar, var_id);
    variable->direct_support =
        UINT64_MAX - variable->direct_support < entry->proposal.direct_support
            ? UINT64_MAX
            : variable->direct_support + entry->proposal.direct_support;
    if (entry->proposal.prior > variable->prior) {
        variable->prior = entry->proposal.prior;
    }
    variable->source_rule_bits |= entry->source_rule_bits;
}

static void candidate_count_add(OspreyGraph *graph,
                                const OspreyRegionId *region, uint8_t kind,
                                uint64_t kept, uint64_t dropped)
{
    OspreyKey key = osprey_kind_region_key(kind, region);
    OspreyKindRegionCount *count = g_hash_table_lookup(graph->kind_region,
                                                       &key);
    if (count == NULL) {
        count = g_new0(OspreyKindRegionCount, 1);
        g_hash_table_insert(graph->kind_region, osprey_key_new(&key), count);
    }
    count->kept = UINT64_MAX - count->kept < kept
        ? UINT64_MAX : count->kept + kept;
    count->dropped = UINT64_MAX - count->dropped < dropped
        ? UINT64_MAX : count->dropped + dropped;
    if (dropped != 0 && graph->limit_rows < UINT64_MAX) {
        graph->limit_rows++;
        log_msg("[osprey] [limit] [kind %u] [region %llx] [kept %llu] "
                "[dropped %llu]\n", (unsigned)kind,
                (unsigned long long)region->site_offset,
                (unsigned long long)count->kept,
                (unsigned long long)count->dropped);
    }
}

OspreyStatus osprey_candidate_select(OspreyContext *ctx,
                                     const OspreyCandidateProposal *proposals,
                                     size_t count)
{
    if (ctx == NULL || ctx->graph == NULL ||
        (count != 0 && proposals == NULL)) {
        graph_set_error(ctx, OSPREY_INVALID_GRAPH);
        return OSPREY_INVALID_GRAPH;
    }
    for (size_t i = 0; i < count; i++) {
        uint16_t rule = proposals[i].source_rule;
        if (rule < OSPREY_RULE_COUNT &&
            ctx->graph->candidate_proposals[rule] != UINT64_MAX) {
            ctx->graph->candidate_proposals[rule]++;
        }
    }
    OspreyStatus extent_status = build_extent_catalog(ctx);
    if (extent_status != OSPREY_OK) {
        graph_set_error(ctx, extent_status);
        return extent_status;
    }

    GArray *entries = g_array_new(FALSE, FALSE, sizeof(CandidateEntry));
    GHashTable *by_key = g_hash_table_new_full(osprey_key_hash,
                                               osprey_key_equal,
                                               osprey_key_free, NULL);
    for (size_t i = 0; i < count; i++) {
        OspreyVarPayload canonical;
        OspreyRegionId primary;
        if (!proposal_valid(ctx, &proposals[i], &canonical, &primary)) {
            g_hash_table_destroy(by_key);
            g_array_free(entries, TRUE);
            graph_set_error(ctx, OSPREY_INVALID_GRAPH);
            return OSPREY_INVALID_GRAPH;
        }
        OspreyKey key = osprey_var_key(proposals[i].predicate_kind,
                                       &canonical);
        gpointer found = g_hash_table_lookup(by_key, &key);
        if (found != NULL) {
            CandidateEntry *entry = &g_array_index(entries, CandidateEntry,
                                                   (gsize)found - 1);
            uint64_t support = proposals[i].direct_support;
            entry->proposal.direct_support =
                UINT64_MAX - entry->proposal.direct_support < support
                    ? UINT64_MAX
                    : entry->proposal.direct_support + support;
            if (proposals[i].prior > entry->proposal.prior) {
                entry->proposal.prior = proposals[i].prior;
            }
            if (proposals[i].source_rule < entry->proposal.source_rule) {
                entry->proposal.source_rule = proposals[i].source_rule;
            }
            entry->source_rule_bits |= 1ULL << proposals[i].source_rule;
            continue;
        }
        CandidateEntry entry;
        memset(&entry, 0, sizeof(entry));
        entry.key = key;
        entry.proposal.predicate_kind = proposals[i].predicate_kind;
        entry.proposal.payload = canonical;
        entry.proposal.direct_support = proposals[i].direct_support;
        entry.proposal.prior = proposals[i].prior;
        entry.proposal.source_rule = proposals[i].source_rule;
        entry.primary_region = primary;
        entry.source_rule_bits = 1ULL << proposals[i].source_rule;
        g_array_append_val(entries, entry);
        g_hash_table_insert(by_key, osprey_key_new(&key),
                            GSIZE_TO_POINTER(entries->len));
    }
    g_hash_table_destroy(by_key);
    g_array_sort(entries, candidate_entry_compare);

    GArray *selected = g_array_new(FALSE, FALSE, sizeof(CandidateEntry));
    GArray *deltas = g_array_new(FALSE, FALSE, sizeof(CandidateBucketDelta));
    uint64_t new_count = 0;
    bool limit_hit = false;
    for (guint i = 0; i < entries->len;) {
        guint begin = i;
        while (i < entries->len &&
               g_array_index(entries, CandidateEntry, i).proposal.predicate_kind ==
                   g_array_index(entries, CandidateEntry, begin)
                       .proposal.predicate_kind &&
               region_compare(&g_array_index(entries, CandidateEntry, i)
                                  .primary_region,
                              &g_array_index(entries, CandidateEntry, begin)
                                  .primary_region) == 0) {
            i++;
        }
        const OspreyRegionId *region =
            &g_array_index(entries, CandidateEntry, begin).primary_region;
        uint8_t kind = g_array_index(entries, CandidateEntry, begin)
                           .proposal.predicate_kind;
        uint64_t bucket_existing = 0;
        for (guint v = 0; v < ctx->graph->vars->len; v++) {
            const OspreyVar *variable = &g_array_index(ctx->graph->vars,
                                                        OspreyVar, v);
            OspreyRegionId variable_region;
            if (proposal_primary_region(variable->kind, &variable->payload,
                                         &variable_region) &&
                variable->kind == kind &&
                region_compare(&variable_region, region) == 0) {
                bucket_existing++;
            }
        }
        uint64_t bucket_kept = bucket_existing;
        uint64_t bucket_new = 0;
        uint64_t bucket_dropped = 0;
        for (guint j = begin; j < i; j++) {
            CandidateEntry *entry = &g_array_index(entries, CandidateEntry, j);
            OspreyKey key = osprey_var_key(entry->proposal.predicate_kind,
                                           &entry->proposal.payload);
            if (g_hash_table_lookup(ctx->graph->var_index, &key) != NULL) {
                continue;
            }
            if (bucket_kept >= ctx->config.max_candidates_per_kind_region) {
                bucket_dropped++;
                limit_hit = true;
                continue;
            }
            bucket_kept++;
            bucket_new++;
            new_count++;
            g_array_append_val(selected, *entry);
        }
        CandidateBucketDelta delta;
        memset(&delta, 0, sizeof(delta));
        delta.region = *region;
        delta.kind = kind;
        delta.kept = bucket_new;
        delta.dropped = bucket_dropped;
        g_array_append_val(deltas, delta);
    }

    bool global_limit_hit =
        (uint64_t)ctx->graph->vars->len > ctx->config.max_variables ||
        ((uint64_t)ctx->graph->vars->len <= ctx->config.max_variables &&
         new_count > ctx->config.max_variables - ctx->graph->vars->len);
    if (global_limit_hit) {
        limit_hit = true;
        for (guint i = 0; i < deltas->len; i++) {
            CandidateBucketDelta *delta = &g_array_index(
                deltas, CandidateBucketDelta, i);
            delta->dropped = UINT64_MAX - delta->dropped < delta->kept
                ? UINT64_MAX : delta->dropped + delta->kept;
            delta->kept = 0;
        }
    } else {
        /* Commit evidence for already-interned duplicates only after the
         * complete batch passes the global cap. */
        for (guint i = 0; i < entries->len; i++) {
            CandidateEntry *entry = &g_array_index(entries, CandidateEntry, i);
            OspreyKey key = osprey_var_key(entry->proposal.predicate_kind,
                                           &entry->proposal.payload);
            gpointer existing = g_hash_table_lookup(ctx->graph->var_index,
                                                     &key);
            if (existing != NULL) {
                candidate_evidence_merge(ctx->graph,
                                         (uint32_t)(uintptr_t)existing - 1,
                                         entry);
            }
        }
        /* Bucket-limit failure retains its deterministic prefix for
         * diagnostics.  The transaction caller still aborts the staged
         * graph before any model can consume it. */
        for (guint i = 0; i < selected->len; i++) {
            CandidateEntry *entry = &g_array_index(selected, CandidateEntry, i);
            OspreyInternResult result = osprey_intern_var(
                ctx, entry->proposal.predicate_kind, &entry->proposal.payload);
            if (result.id == UINT32_MAX) {
                graph_set_error(ctx, OSPREY_INVALID_GRAPH);
                g_array_free(deltas, TRUE);
                g_array_free(selected, TRUE);
                g_array_free(entries, TRUE);
                return ctx->last_status;
            }
            candidate_evidence_merge(ctx->graph, result.id, entry);
        }
    }
    for (guint i = 0; i < deltas->len; i++) {
        const CandidateBucketDelta *delta = &g_array_index(
            deltas, CandidateBucketDelta, i);
        candidate_count_add(ctx->graph, &delta->region, delta->kind,
                            delta->kept, delta->dropped);
    }
    if (limit_hit) {
        graph_set_error(ctx, OSPREY_LIMIT_EXCEEDED);
    }

    g_array_free(deltas, TRUE);
    g_array_free(selected, TRUE);
    g_array_free(entries, TRUE);
    if (limit_hit) return OSPREY_LIMIT_EXCEEDED;
    return OSPREY_OK;
}

/* ------------------------------------------------------------------ */
/* Canonical graph dump                                                 */
/* ------------------------------------------------------------------ */

typedef struct VarDisplay {
    uint32_t id;
    uint8_t kind;
    OspreyVarPayload payload;
} VarDisplay;

typedef struct FactorDisplayContext {
    const uint32_t *ordinals;
} FactorDisplayContext;

typedef struct BucketDisplay {
    OspreyKey key;
    OspreyKindRegionCount count;
} BucketDisplay;

static int var_display_compare(gconstpointer ap, gconstpointer bp)
{
    const VarDisplay *a = ap;
    const VarDisplay *b = bp;
    int c = cmp_u64(a->kind, b->kind);
    return c != 0 ? c : osprey_var_payload_compare(a->kind, &a->payload, &b->payload);
}

static int factor_display_compare(gconstpointer ap, gconstpointer bp,
                                  gpointer user_data)
{
    const OspreyFactor *a = *(OspreyFactor *const *)ap;
    const OspreyFactor *b = *(OspreyFactor *const *)bp;
    const FactorDisplayContext *context = user_data;
    int c = cmp_u64(a->stage, b->stage);
    if (c != 0) return c;
    c = cmp_u64(a->rule, b->rule);
    if (c != 0) return c;
    c = cmp_u64(a->potential_kind, b->potential_kind);
    if (c != 0) return c;
    c = cmp_u64(a->negative, b->negative);
    if (c != 0) return c;
    uint64_t ap_bits, bp_bits;
    memcpy(&ap_bits, &a->p, sizeof(ap_bits));
    memcpy(&bp_bits, &b->p, sizeof(bp_bits));
    c = cmp_u64(ap_bits, bp_bits);
    if (c != 0) return c;
    c = cmp_u64(a->head_idx, b->head_idx);
    if (c != 0) return c;
    c = cmp_u64(a->num_vars, b->num_vars);
    if (c != 0) return c;
    for (uint32_t i = 0; i < a->num_vars; i++) {
        c = cmp_u64(context->ordinals[a->var_ids[i]],
                    context->ordinals[b->var_ids[i]]);
        if (c != 0) return c;
    }
    return 0;
}

static void dump_region(FILE *out, const OspreyRegionId *region)
{
    fprintf(out, "r%u:%016" PRIx64 ":%016" PRIx64,
            (unsigned)region->kind, region->code_image_id,
            region->site_offset);
}

static void dump_address(FILE *out, const OspreyAddress *address)
{
    dump_region(out, &address->region);
    fprintf(out, ":%016" PRIx64, (uint64_t)address->offset);
}

static void dump_chunk(FILE *out, const OspreyChunk *chunk)
{
    fputc('{', out);
    dump_address(out, &chunk->address);
    fprintf(out, ":%" PRIu64 "}", chunk->size);
}

static int dump_chunk_compare(const OspreyChunk *a, const OspreyChunk *b)
{
    return chunk_compare(a, b);
}

static int dump_address_compare(const OspreyAddress *a,
                                const OspreyAddress *b)
{
    return address_compare(a, b);
}

static int dump_region_compare(const OspreyRegionId *a,
                               const OspreyRegionId *b)
{
    return region_compare(a, b);
}

static int dump_insn_chunk_compare(gconstpointer ap, gconstpointer bp)
{
    const OspreyInsnChunkRelation *a = ap;
    const OspreyInsnChunkRelation *b = bp;
    int c = cmp_u64(a->pc, b->pc);
    return c != 0 ? c : dump_chunk_compare(&a->chunk, &b->chunk);
}

static int dump_chunk_relation_compare(gconstpointer ap, gconstpointer bp)
{
    const OspreyChunkRelation *a = ap;
    const OspreyChunkRelation *b = bp;
    return dump_chunk_compare(&a->chunk, &b->chunk);
}

static int dump_insn_region_compare(gconstpointer ap, gconstpointer bp)
{
    const OspreyInsnRegionRelation *a = ap;
    const OspreyInsnRegionRelation *b = bp;
    int c = cmp_u64(a->pc, b->pc);
    return c != 0 ? c : dump_region_compare(&a->region, &b->region);
}

static int dump_insn_region_address_compare(gconstpointer ap,
                                            gconstpointer bp)
{
    const OspreyInsnRegionAddressRelation *a = ap;
    const OspreyInsnRegionAddressRelation *b = bp;
    int c = cmp_u64(a->pc, b->pc);
    if (c != 0) return c;
    c = dump_region_compare(&a->region, &b->region);
    if (c != 0) return c;
    c = dump_address_compare(&a->address, &b->address);
    return c != 0 ? c : cmp_u64(a->count, b->count);
}

static int dump_alloc_compare(gconstpointer ap, gconstpointer bp)
{
    const OspreyAllocRelation *a = ap;
    const OspreyAllocRelation *b = bp;
    int c = cmp_u64(a->site_pc, b->site_pc);
    return c != 0 ? c : cmp_u64(a->size, b->size);
}

static int dump_hint_compare(gconstpointer ap, gconstpointer bp)
{
    const OspreyHintRelation *a = ap;
    const OspreyHintRelation *b = bp;
    int c = dump_address_compare(&a->a1, &b->a1);
    if (c != 0) return c;
    c = dump_address_compare(&a->a2, &b->a2);
    if (c != 0) return c;
    c = cmp_i64(a->size, b->size);
    if (c != 0) return c;
    c = cmp_u64(a->kind, b->kind);
    return c != 0 ? c : cmp_u64(a->witness_count, b->witness_count);
}

static GArray *dump_sorted_copy(const GArray *source, guint element_size,
                                GCompareFunc compare)
{
    if (source == NULL) return g_array_new(FALSE, FALSE, element_size);
    GArray *copy = g_array_sized_new(FALSE, FALSE, element_size, source->len);
    if (source->len != 0) {
        g_array_append_vals(copy, source->data, source->len);
        g_array_sort(copy, compare);
    }
    return copy;
}

static void dump_relation_rows(const OspreyRelations *relations, FILE *out)
{
    if (relations == NULL) return;
    GArray *r01 = dump_sorted_copy(relations->r01_accessed,
                                   sizeof(OspreyInsnChunkRelation),
                                   dump_insn_chunk_compare);
    GArray *r02 = dump_sorted_copy(relations->r02_accessed,
                                   sizeof(OspreyChunkRelation),
                                   dump_chunk_relation_compare);
    GArray *r03 = dump_sorted_copy(relations->r03_single_chunk,
                                   sizeof(OspreyInsnRegionRelation),
                                   dump_insn_region_compare);
    GArray *r04 = dump_sorted_copy(relations->r04_multi_chunk,
                                   sizeof(OspreyInsnRegionRelation),
                                   dump_insn_region_compare);
    GArray *r05 = dump_sorted_copy(relations->r05_high_address,
                                   sizeof(OspreyInsnRegionAddressRelation),
                                   dump_insn_region_address_compare);
    GArray *r06 = dump_sorted_copy(relations->r06_low_address,
                                   sizeof(OspreyInsnRegionAddressRelation),
                                   dump_insn_region_address_compare);
    GArray *r07 = dump_sorted_copy(relations->r07_most_frequent,
                                   sizeof(OspreyInsnRegionAddressRelation),
                                   dump_insn_region_address_compare);
    GArray *r08 = dump_sorted_copy(relations->r08_constant_alloc,
                                   sizeof(OspreyAllocRelation),
                                   dump_alloc_compare);
    GArray *r09 = dump_sorted_copy(relations->r09_alloc_unit,
                                   sizeof(OspreyAllocRelation),
                                   dump_alloc_compare);
    GArray *r10 = dump_sorted_copy(relations->r10_data_flow,
                                   sizeof(OspreyHintRelation),
                                   dump_hint_compare);
    GArray *r11 = dump_sorted_copy(relations->r11_unified_access,
                                   sizeof(OspreyHintRelation),
                                   dump_hint_compare);
    GArray *r12 = dump_sorted_copy(relations->r12_points_to,
                                   sizeof(OspreyHintRelation),
                                   dump_hint_compare);
#define DUMP_IC(_name, _array) do { \
    if ((_array) == NULL) break; \
    for (guint i = 0; i < (_array)->len; i++) { \
        const OspreyInsnChunkRelation *r = &g_array_index( \
            (_array), OspreyInsnChunkRelation, i); \
        fprintf(out, "%s pc=%016" PRIx64 " chunk=", _name, r->pc); \
        dump_chunk(out, &r->chunk); \
        fputc('\n', out); \
    } \
} while (0)
    DUMP_IC("R01", r01);
#undef DUMP_IC
    if (r02 != NULL) {
        for (guint i = 0; i < r02->len; i++) {
            const OspreyChunkRelation *r = &g_array_index(
                r02, OspreyChunkRelation, i);
            fputs("R02 chunk=", out);
            dump_chunk(out, &r->chunk);
            fputc('\n', out);
        }
    }
#define DUMP_IR(_name, _array) do { \
    if ((_array) == NULL) break; \
    for (guint i = 0; i < (_array)->len; i++) { \
        const OspreyInsnRegionRelation *r = &g_array_index( \
            (_array), OspreyInsnRegionRelation, i); \
        fprintf(out, "%s pc=%016" PRIx64 " region=", _name, r->pc); \
        dump_region(out, &r->region); \
        fputc('\n', out); \
    } \
} while (0)
    DUMP_IR("R03", r03);
    DUMP_IR("R04", r04);
#undef DUMP_IR
#define DUMP_IRA(_name, _array) do { \
    if ((_array) == NULL) break; \
    for (guint i = 0; i < (_array)->len; i++) { \
        const OspreyInsnRegionAddressRelation *r = &g_array_index( \
            (_array), OspreyInsnRegionAddressRelation, i); \
        fprintf(out, "%s pc=%016" PRIx64 " region=", _name, r->pc); \
        dump_region(out, &r->region); \
        fputs(" address=", out); \
        dump_address(out, &r->address); \
        fprintf(out, " count=%" PRIu32 "\n", r->count); \
    } \
} while (0)
    DUMP_IRA("R05", r05);
    DUMP_IRA("R06", r06);
    DUMP_IRA("R07", r07);
#undef DUMP_IRA
#define DUMP_ALLOC(_name, _array) do { \
    if ((_array) == NULL) break; \
    for (guint i = 0; i < (_array)->len; i++) { \
        const OspreyAllocRelation *r = &g_array_index( \
            (_array), OspreyAllocRelation, i); \
        fprintf(out, "%s site=%016" PRIx64 " size=%" PRIu64 "\n", \
                _name, r->site_pc, r->size); \
    } \
} while (0)
    DUMP_ALLOC("R08", r08);
    DUMP_ALLOC("R09", r09);
#undef DUMP_ALLOC
#define DUMP_HINT(_name, _array) do { \
    if ((_array) == NULL) break; \
    for (guint i = 0; i < (_array)->len; i++) { \
        const OspreyHintRelation *r = &g_array_index( \
            (_array), OspreyHintRelation, i); \
        fprintf(out, "%s a1=", _name); \
        dump_address(out, &r->a1); \
        fputs(" a2=", out); \
        dump_address(out, &r->a2); \
        fprintf(out, " size=%" PRId64 " witnesses=%" PRIu64 "\n", \
                r->size, r->witness_count); \
    } \
} while (0)
    DUMP_HINT("R10", r10);
    DUMP_HINT("R11", r11);
    DUMP_HINT("R12", r12);
#undef DUMP_HINT
    g_array_free(r12, TRUE);
    g_array_free(r11, TRUE);
    g_array_free(r10, TRUE);
    g_array_free(r09, TRUE);
    g_array_free(r08, TRUE);
    g_array_free(r07, TRUE);
    g_array_free(r06, TRUE);
    g_array_free(r05, TRUE);
    g_array_free(r04, TRUE);
    g_array_free(r03, TRUE);
    g_array_free(r02, TRUE);
    g_array_free(r01, TRUE);
}

static void dump_variable(FILE *out, uint32_t ordinal, const OspreyVar *var)
{
    uint64_t prior_bits;
    memcpy(&prior_bits, &var->prior, sizeof(prior_bits));
    fprintf(out, "P %u kind=%u hard_false=%u support=%" PRIu64
                 " priorbits=%016" PRIx64 " sources=%016" PRIx64 " ",
            ordinal, (unsigned)var->kind, (unsigned)var->hard_false,
            var->direct_support, prior_bits, var->source_rule_bits);
    switch (var->kind) {
    case OSPREY_PRED_PRIMITIVE_VAR:
    case OSPREY_PRED_SCALAR:
        fputs("chunk=", out);
        dump_chunk(out, &var->payload.chunk);
        break;
    case OSPREY_PRED_PRIMITIVE_ACCESS:
        fprintf(out, "pc=%016" PRIx64 " chunk=",
                var->payload.prim_access.insn_pc);
        dump_chunk(out, &var->payload.prim_access.chunk);
        break;
    case OSPREY_PRED_UNFOLDABLE_HEAP:
    case OSPREY_PRED_FOLDABLE_HEAP:
        fputs("region=", out);
        dump_region(out, &var->payload.heap_fold.region);
        fprintf(out, " size=%" PRIu64, var->payload.heap_fold.size);
        break;
    case OSPREY_PRED_HOMO_SEGMENT:
    case OSPREY_PRED_ARRAY:
        fputs("a1=", out);
        dump_address(out, &var->payload.segment.a1);
        fputs(" a2=", out);
        dump_address(out, &var->payload.segment.a2);
        fprintf(out, " size=%" PRId64, var->payload.segment.size);
        break;
    case OSPREY_PRED_ARRAY_START:
        fputs("address=", out);
        dump_address(out, &var->payload.addr);
        break;
    case OSPREY_PRED_FIELD_OF:
    case OSPREY_PRED_POINTER:
        fputs("chunk=", out);
        dump_chunk(out, &var->payload.attached.chunk);
        fputs(" base=", out);
        dump_address(out, &var->payload.attached.base);
        break;
    default:
        break;
    }
    fputc('\n', out);
}

static int bucket_display_compare(gconstpointer ap, gconstpointer bp)
{
    const BucketDisplay *a = ap;
    const BucketDisplay *b = bp;
    return key_compare(&a->key, &b->key);
}

bool osprey_graph_dump_file(const OspreyContext *ctx, FILE *out)
{
    if (ctx == NULL || ctx->graph == NULL || out == NULL) return false;
    const OspreyGraph *graph = ctx->graph;
    GArray *ordered_vars = g_array_new(FALSE, FALSE, sizeof(VarDisplay));
    uint32_t *ordinals = g_new(uint32_t, graph->vars->len);
    for (guint i = 0; i < graph->vars->len; i++) {
        const OspreyVar *var = &g_array_index(graph->vars, OspreyVar, i);
        VarDisplay display;
        memset(&display, 0, sizeof(display));
        display.id = var->id;
        display.kind = var->kind;
        display.payload = var->payload;
        g_array_append_val(ordered_vars, display);
    }
    g_array_sort(ordered_vars, var_display_compare);
    for (guint i = 0; i < ordered_vars->len; i++) {
        const VarDisplay *display = &g_array_index(ordered_vars, VarDisplay, i);
        ordinals[display->id] = i;
    }

    fprintf(out, "OSPREY_GRAPH 1\n");
    fputs("RELATIONS\n", out);
    dump_relation_rows(ctx->relations, out);
    fprintf(out, "PREDICATES %u\n", graph->vars->len);
    for (guint i = 0; i < ordered_vars->len; i++) {
        const VarDisplay *display = &g_array_index(ordered_vars, VarDisplay, i);
        const OspreyVar *var = &g_array_index(graph->vars, OspreyVar,
                                              display->id);
        dump_variable(out, i, var);
    }

    GArray *ordered_factors = g_array_new(FALSE, FALSE, sizeof(OspreyFactor *));
    for (guint i = 0; i < graph->factors->len; i++) {
        OspreyFactor *factor = g_array_index(graph->factors, OspreyFactor *, i);
        g_array_append_val(ordered_factors, factor);
    }
    FactorDisplayContext factor_context = { ordinals };
    g_array_sort_with_data(ordered_factors, factor_display_compare,
                           &factor_context);
    fprintf(out, "FACTORS %u\n", graph->factors->len);
    for (guint i = 0; i < ordered_factors->len; i++) {
        const OspreyFactor *factor = g_array_index(ordered_factors,
                                                   OspreyFactor *, i);
        uint64_t p_bits;
        memcpy(&p_bits, &factor->p, sizeof(p_bits));
        fprintf(out, "F %u stage=%u rule=%u potential=%u negative=%u "
                     "pbits=%016" PRIx64 " head=",
                i, (unsigned)factor->stage, (unsigned)factor->rule,
                (unsigned)factor->potential_kind, (unsigned)factor->negative,
                p_bits);
        if (factor->head_idx == UINT16_MAX) {
            fputs("none", out);
        } else {
            fprintf(out, "%u", (unsigned)factor->head_idx);
        }
        fprintf(out, " arity=%u vars=", factor->num_vars);
        for (uint32_t j = 0; j < factor->num_vars; j++) {
            if (j != 0) fputc(',', out);
            fprintf(out, "%u", ordinals[factor->var_ids[j]]);
        }
        fputc('\n', out);
    }

    GArray *buckets = g_array_new(FALSE, FALSE, sizeof(BucketDisplay));
    GHashTableIter iterator;
    gpointer bucket_key, bucket_value;
    g_hash_table_iter_init(&iterator, graph->kind_region);
    while (g_hash_table_iter_next(&iterator, &bucket_key, &bucket_value)) {
        BucketDisplay row;
        row.key = *(const OspreyKey *)bucket_key;
        row.count = *(const OspreyKindRegionCount *)bucket_value;
        g_array_append_val(buckets, row);
    }
    g_array_sort(buckets, bucket_display_compare);
    fputs("CANDIDATE_BUCKETS\n", out);
    uint64_t candidate_kept = 0;
    uint64_t candidate_dropped = 0;
    for (guint i = 0; i < buckets->len; i++) {
        const BucketDisplay *row = &g_array_index(buckets, BucketDisplay, i);
        OspreyRegionId region;
        memset(&region, 0, sizeof(region));
        region.kind = (OspreyRegionKind)row->key.w[0];
        region.code_image_id = row->key.w[1];
        region.site_offset = row->key.w[2];
        fprintf(out, "B kind=%u region=", (unsigned)row->key.w[3]);
        dump_region(out, &region);
        fprintf(out, " kept=%" PRIu64 " dropped=%" PRIu64 "\n",
                row->count.kept, row->count.dropped);
        candidate_kept = UINT64_MAX - candidate_kept < row->count.kept
            ? UINT64_MAX : candidate_kept + row->count.kept;
        candidate_dropped = UINT64_MAX - candidate_dropped < row->count.dropped
            ? UINT64_MAX : candidate_dropped + row->count.dropped;
    }
    fprintf(out, "TOTALS vars=%u factors=%u hints=%" PRIu64
                 " limit_rows=%" PRIu64 " candidate_kept=%" PRIu64
                 " candidate_dropped=%" PRIu64 "\n", graph->vars->len,
            graph->factors->len, graph->hint_instances, graph->limit_rows,
            candidate_kept, candidate_dropped);

    g_array_free(buckets, TRUE);
    g_array_free(ordered_factors, TRUE);
    g_free(ordinals);
    g_array_free(ordered_vars, TRUE);
    return ferror(out) == 0;
}

bool osprey_graph_dump(const OspreyContext *ctx, const char *path)
{
    if (path == NULL || path[0] == '\0') return false;
    FILE *out = fopen(path, "w");
    if (out == NULL) return false;
    bool ok = osprey_graph_dump_file(ctx, out);
    if (fclose(out) != 0) ok = false;
    return ok;
}
