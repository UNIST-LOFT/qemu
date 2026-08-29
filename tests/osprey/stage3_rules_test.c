/* Stage 3 CA/CB/CC/CD rule tests. */

#include "osprey.h"
#include "osprey-internal.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned failures;
static unsigned registered;
static unsigned executed;

#define CHECK(condition, message) do {                                      \
    if (!(condition)) {                                                      \
        fprintf(stderr, "FAIL: %s (line %d)\n", (message), __LINE__);     \
        failures++;                                                          \
    }                                                                            \
} while (0)

#define RUN(test) do {                                                       \
    registered++;                                                            \
    test();                                                                  \
    executed++;                                                              \
} while (0)

static OspreyConfig rules_config(void)
{
    OspreyConfig config;
    memset(&config, 0, sizeof(config));
    config.enabled = true;
    config.shared_bytes = 1u << 20;
    config.max_facts = 4096;
    config.max_chunks_per_region = 512;
    config.max_candidates_per_kind_region = 4096;
    config.max_variables = 4096;
    config.max_factors = 8192;
    config.max_exact_clique_vars = 20;
    config.report_threshold = 0.5;
    return config;
}

static OspreyRegionId region(OspreyRegionKind kind, uint64_t site)
{
    OspreyRegionId result;
    memset(&result, 0, sizeof(result));
    result.kind = kind;
    result.site_offset = site;
    return result;
}

static OspreyAddress address(OspreyRegionId region_id, int64_t offset)
{
    OspreyAddress result;
    memset(&result, 0, sizeof(result));
    result.region = region_id;
    result.offset = offset;
    return result;
}

static OspreyChunk chunk(OspreyRegionId region_id, int64_t offset,
                         uint64_t size)
{
    OspreyChunk result;
    memset(&result, 0, sizeof(result));
    result.address = address(region_id, offset);
    result.size = size;
    return result;
}

static OspreyContext *new_context(void)
{
    OspreyConfig config = rules_config();
    OspreyContext *ctx = osprey_new(&config);
    ctx->total_samples = 4;
    osprey_tx_begin(ctx);
    ctx->graph = osprey_graph_new();
    return ctx;
}

static void add_logical(OspreyContext *ctx, uint64_t pc,
                        const OspreyChunk *value, uint32_t dynamic_count,
                        uint32_t sample_support)
{
    OspreyAccessFact access;
    memset(&access, 0, sizeof(access));
    access.pc = pc;
    access.chunk = *value;
    access.dynamic_count = dynamic_count;
    access.sample_support = sample_support;
    g_array_append_val(ctx->access_facts, access);

    OspreyLogicalAccess logical;
    memset(&logical, 0, sizeof(logical));
    logical.pc = pc;
    logical.chunk = *value;
    logical.dynamic_count = dynamic_count;
    logical.sample_support = sample_support;
    g_array_append_val(ctx->logical_access_facts, logical);
}

static void add_logical_value(OspreyContext *ctx, uint64_t pc,
                              OspreyChunk value, uint32_t dynamic_count,
                              uint32_t sample_support)
{
    add_logical(ctx, pc, &value, dynamic_count, sample_support);
}

static bool build_base(OspreyContext *ctx)
{
    OspreyStatus status = osprey_stage3_base(ctx);
    CHECK(status == OSPREY_OK, "base construction succeeds");
    return status == OSPREY_OK;
}

static bool build_secondary(OspreyContext *ctx)
{
    if (!build_base(ctx)) return false;
    OspreyStatus status = osprey_stage3_secondary(ctx);
    CHECK(status == OSPREY_OK, "secondary construction succeeds");
    return status == OSPREY_OK;
}

static unsigned rule_count(const OspreyContext *ctx, uint16_t rule)
{
    unsigned count = 0;
    for (guint i = 0; i < ctx->graph->factors->len; i++) {
        const OspreyFactor *factor = g_array_index(ctx->graph->factors,
                                                    OspreyFactor *, i);
        if (factor->rule == rule) count++;
    }
    return count;
}

static const OspreyFactor *first_rule(const OspreyContext *ctx, uint16_t rule)
{
    for (guint i = 0; i < ctx->graph->factors->len; i++) {
        const OspreyFactor *factor = g_array_index(ctx->graph->factors,
                                                    OspreyFactor *, i);
        if (factor->rule == rule) return factor;
    }
    return NULL;
}

static uint32_t variable_id(const OspreyContext *ctx, uint8_t kind,
                            const OspreyVarPayload *payload)
{
    if (ctx == NULL || ctx->graph == NULL || payload == NULL) return UINT32_MAX;
    OspreyKey key = osprey_var_key(kind, payload);
    gpointer value = g_hash_table_lookup(ctx->graph->var_index, &key);
    return value == NULL ? UINT32_MAX : (uint32_t)(uintptr_t)value - 1;
}

static uint32_t chunk_variable_id(const OspreyContext *ctx, uint8_t kind,
                                  const OspreyChunk *value)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.chunk = *value;
    return variable_id(ctx, kind, &payload);
}

static uint32_t chunk_variable_id_value(const OspreyContext *ctx,
                                        uint8_t kind,
                                        OspreyRegionId region_id,
                                        int64_t offset, uint64_t size)
{
    OspreyChunk value = chunk(region_id, offset, size);
    return chunk_variable_id(ctx, kind, &value);
}

static uint32_t access_variable_id(const OspreyContext *ctx, uint64_t pc,
                                   const OspreyChunk *value)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.prim_access.chunk = *value;
    payload.prim_access.insn_pc = pc;
    return variable_id(ctx, OSPREY_PRED_PRIMITIVE_ACCESS, &payload);
}

static uint32_t array_variable_id(const OspreyContext *ctx,
                                  OspreyRegionId region_id, int64_t lo,
                                  int64_t hi, int64_t stride)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.segment.a1 = address(region_id, lo);
    payload.segment.a2 = address(region_id, hi);
    payload.segment.size = stride;
    return variable_id(ctx, OSPREY_PRED_ARRAY, &payload);
}

static uint32_t start_variable_id(const OspreyContext *ctx,
                                  const OspreyAddress *value)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.addr = *value;
    return variable_id(ctx, OSPREY_PRED_ARRAY_START, &payload);
}

static uint32_t field_variable_id(const OspreyContext *ctx,
                                  const OspreyChunk *value,
                                  const OspreyAddress *base)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.attached.chunk = *value;
    payload.attached.base = *base;
    return variable_id(ctx, OSPREY_PRED_FIELD_OF, &payload);
}

static bool probability_bits_equal(double actual, double expected)
{
    uint64_t actual_bits;
    uint64_t expected_bits;
    memcpy(&actual_bits, &actual, sizeof(actual_bits));
    memcpy(&expected_bits, &expected, sizeof(expected_bits));
    return actual_bits == expected_bits;
}

static bool factor_exact(const OspreyContext *ctx, uint16_t rule,
                         uint8_t stage, uint8_t potential_kind,
                         bool negative, double probability,
                         uint16_t head_idx, const uint32_t *var_ids,
                         uint32_t num_vars)
{
    for (guint i = 0; i < ctx->graph->factors->len; i++) {
        const OspreyFactor *factor = g_array_index(ctx->graph->factors,
                                                    OspreyFactor *, i);
        if (factor->rule != rule || factor->stage != stage ||
            factor->potential_kind != potential_kind ||
            factor->negative != (uint8_t)negative ||
            !probability_bits_equal(factor->p, probability) ||
            factor->head_idx != head_idx || factor->num_vars != num_vars) {
            continue;
        }
        bool matches = true;
        for (uint32_t j = 0; j < num_vars; j++) {
            if (factor->var_ids[j] != var_ids[j]) {
                matches = false;
                break;
            }
        }
        if (matches) return true;
    }
    return false;
}

static void expect_factor(const OspreyContext *ctx, uint16_t rule,
                          uint8_t stage, uint8_t potential_kind,
                          bool negative, double probability,
                          uint16_t head_idx, const uint32_t *var_ids,
                          uint32_t num_vars, const char *message)
{
    CHECK(factor_exact(ctx, rule, stage, potential_kind, negative,
                       probability, head_idx, var_ids, num_vars), message);
}

typedef struct FactorExpectation {
    uint8_t stage;
    uint8_t potential_kind;
    bool negative;
    double probability;
    uint16_t head_idx;
    const uint32_t *var_ids;
    uint32_t num_vars;
} FactorExpectation;

static bool factor_matches_expectation(const OspreyFactor *factor,
                                       const FactorExpectation *expected)
{
    if (factor->stage != expected->stage ||
        factor->potential_kind != expected->potential_kind ||
        factor->negative != (uint8_t)expected->negative ||
        !probability_bits_equal(factor->p, expected->probability) ||
        factor->head_idx != expected->head_idx ||
        factor->num_vars != expected->num_vars) {
        return false;
    }
    for (uint32_t i = 0; i < expected->num_vars; i++) {
        if (factor->var_ids[i] != expected->var_ids[i]) return false;
    }
    return true;
}

static bool factor_block_exact(const OspreyContext *ctx, uint16_t rule,
                               const FactorExpectation *expected,
                               guint expected_count)
{
    guint actual_count = 0;
    for (guint i = 0; i < ctx->graph->factors->len; i++) {
        const OspreyFactor *factor = g_array_index(ctx->graph->factors,
                                                    OspreyFactor *, i);
        if (factor->rule == rule) actual_count++;
    }
    if (actual_count != expected_count) return false;

    bool *matched = g_new0(bool, expected_count);
    bool equal = true;
    for (guint i = 0; i < ctx->graph->factors->len && equal; i++) {
        const OspreyFactor *factor = g_array_index(ctx->graph->factors,
                                                    OspreyFactor *, i);
        if (factor->rule != rule) continue;
        bool found = false;
        for (guint j = 0; j < expected_count; j++) {
            if (!matched[j] && factor_matches_expectation(factor,
                                                           &expected[j])) {
                matched[j] = true;
                found = true;
                break;
            }
        }
        equal = found;
    }
    g_free(matched);
    return equal;
}

static void expect_factor_block(const OspreyContext *ctx, uint16_t rule,
                                const FactorExpectation *expected,
                                guint expected_count, const char *message)
{
    CHECK(factor_block_exact(ctx, rule, expected, expected_count), message);
}

static void expect_candidate_proposals(const OspreyContext *ctx,
                                       uint16_t rule, uint64_t expected,
                                       const char *message)
{
    CHECK(ctx->graph->candidate_proposals[rule] == expected, message);
}

static void expect_candidate_accounting(const OspreyContext *ctx,
                                        uint16_t rule,
                                        uint64_t expected_proposals,
                                        uint64_t expected_kept,
                                        uint64_t expected_dropped,
                                        const char *message)
{
    uint64_t kept = 0;
    uint64_t dropped = 0;
    GHashTableIter iterator;
    gpointer key_pointer;
    gpointer value_pointer;
    g_hash_table_iter_init(&iterator, ctx->graph->kind_region);
    while (g_hash_table_iter_next(&iterator, &key_pointer, &value_pointer)) {
        const OspreyKindRegionCount *count = value_pointer;
        kept += count->kept;
        dropped += count->dropped;
    }
    CHECK(ctx->graph->candidate_proposals[rule] == expected_proposals &&
          kept == expected_kept && dropped == expected_dropped, message);
}

static bool candidate_accounting_equal(const OspreyGraph *left,
                                       const OspreyGraph *right)
{
    for (uint16_t rule = 0; rule < OSPREY_RULE_COUNT; rule++) {
        if (left->candidate_proposals[rule] !=
            right->candidate_proposals[rule]) {
            return false;
        }
    }
    if (g_hash_table_size(left->kind_region) !=
        g_hash_table_size(right->kind_region) ||
        left->limit_rows != right->limit_rows) {
        return false;
    }
    GHashTableIter iterator;
    gpointer key_pointer;
    gpointer value_pointer;
    g_hash_table_iter_init(&iterator, left->kind_region);
    while (g_hash_table_iter_next(&iterator, &key_pointer, &value_pointer)) {
        const OspreyKindRegionCount *left_count = value_pointer;
        const OspreyKindRegionCount *right_count = g_hash_table_lookup(
            right->kind_region, key_pointer);
        if (right_count == NULL || left_count->kept != right_count->kept ||
            left_count->dropped != right_count->dropped) {
            return false;
        }
    }
    return true;
}

static bool variable_semantic_equal(const OspreyVar *left,
                                    const OspreyVar *right)
{
    if (left == NULL || right == NULL || left->kind != right->kind ||
        left->hard_false != right->hard_false ||
        left->region_limit_hit != right->region_limit_hit ||
        left->direct_support != right->direct_support ||
        left->source_rule_bits != right->source_rule_bits ||
        !probability_bits_equal(left->prior, right->prior)) {
        return false;
    }
    OspreyKey left_key = osprey_var_key(left->kind, &left->payload);
    OspreyKey right_key = osprey_var_key(right->kind, &right->payload);
    return osprey_key_equal(&left_key, &right_key);
}

static bool variable_sets_equal(const OspreyContext *left,
                                const OspreyContext *right)
{
    if (left->graph->vars->len != right->graph->vars->len) return false;
    bool *matched = g_new0(bool, right->graph->vars->len);
    bool equal = true;
    for (guint i = 0; i < left->graph->vars->len && equal; i++) {
        const OspreyVar *left_var = &g_array_index(left->graph->vars,
                                                    OspreyVar, i);
        bool found = false;
        for (guint j = 0; j < right->graph->vars->len; j++) {
            const OspreyVar *right_var = &g_array_index(right->graph->vars,
                                                         OspreyVar, j);
            if (!matched[j] && variable_semantic_equal(left_var, right_var)) {
                matched[j] = true;
                found = true;
                break;
            }
        }
        equal = found;
    }
    g_free(matched);
    return equal;
}

static const OspreyVar *find_semantic_variable(const OspreyContext *ctx,
                                                 const OspreyVar *needle)
{
    for (guint i = 0; i < ctx->graph->vars->len; i++) {
        const OspreyVar *candidate = &g_array_index(ctx->graph->vars,
                                                     OspreyVar, i);
        if (variable_semantic_equal(needle, candidate)) return candidate;
    }
    return NULL;
}

static bool factor_semantic_equal(const OspreyContext *left_ctx,
                                  const OspreyFactor *left,
                                  const OspreyContext *right_ctx,
                                  const OspreyFactor *right)
{
    if (left->rule != right->rule || left->stage != right->stage ||
        left->potential_kind != right->potential_kind ||
        left->negative != right->negative || left->head_idx != right->head_idx ||
        !probability_bits_equal(left->p, right->p) ||
        left->num_vars != right->num_vars) {
        return false;
    }
    for (uint32_t i = 0; i < left->num_vars; i++) {
        const OspreyVar *left_var = &g_array_index(left_ctx->graph->vars,
                                                    OspreyVar,
                                                    left->var_ids[i]);
        const OspreyVar *right_var = find_semantic_variable(right_ctx,
                                                              left_var);
        if (right_var == NULL || right_var->id != right->var_ids[i]) {
            return false;
        }
    }
    return true;
}

static bool rule_factor_sets_equal(const OspreyContext *left,
                                   const OspreyContext *right,
                                   uint16_t rule)
{
    guint left_count = rule_count(left, rule);
    guint right_count = rule_count(right, rule);
    if (left_count != right_count) return false;
    bool *matched = g_new0(bool, right->graph->factors->len);
    bool equal = true;
    for (guint i = 0; i < left->graph->factors->len && equal; i++) {
        const OspreyFactor *left_factor = g_array_index(left->graph->factors,
                                                         OspreyFactor *, i);
        if (left_factor->rule != rule) continue;
        bool found = false;
        for (guint j = 0; j < right->graph->factors->len; j++) {
            const OspreyFactor *right_factor = g_array_index(
                right->graph->factors, OspreyFactor *, j);
            if (!matched[j] && right_factor->rule == rule &&
                factor_semantic_equal(left, left_factor, right, right_factor)) {
                matched[j] = true;
                found = true;
                break;
            }
        }
        equal = found;
    }
    g_free(matched);
    return equal;
}

static void add_extent(OspreyContext *ctx, const OspreyChunk *value)
{
    OspreyAccessFact access;
    memset(&access, 0, sizeof(access));
    access.chunk = *value;
    access.dynamic_count = 1;
    access.sample_support = 1;
    g_array_append_val(ctx->access_facts, access);
}

static void add_allocation(OspreyContext *ctx, uint64_t site,
                            uint64_t requested_size)
{
    OspreyMallocFact fact;
    memset(&fact, 0, sizeof(fact));
    fact.site_pc = site;
    fact.requested_size = requested_size;
    fact.sample_support = 1;
    g_array_append_val(ctx->alloc_facts, fact);
}

static void add_copy_fact(OspreyContext *ctx, OspreyChunk source,
                          OspreyChunk destination)
{
    OspreyCopyFact fact;
    memset(&fact, 0, sizeof(fact));
    fact.source = source;
    fact.destination = destination;
    fact.sample_support = 1;
    g_array_append_val(ctx->copy_facts, fact);
}

static void add_base_fact(OspreyContext *ctx, OspreyChunk value,
                          OspreyAddress base)
{
    OspreyBaseFact fact;
    memset(&fact, 0, sizeof(fact));
    fact.chunk = value;
    fact.base = base;
    fact.sample_support = 1;
    g_array_append_val(ctx->base_facts, fact);
}

static void add_points_fact(OspreyContext *ctx, OspreyChunk pointer,
                            OspreyAddress target)
{
    OspreyPointsToFact fact;
    memset(&fact, 0, sizeof(fact));
    fact.pointer_chunk = pointer;
    fact.target = target;
    fact.sample_support = 1;
    g_array_append_val(ctx->points_facts, fact);
}

static OspreyInternResult seed_heap_fold(OspreyContext *ctx, uint8_t kind,
                                         OspreyRegionId region_id,
                                         uint64_t size)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.heap_fold.region = region_id;
    payload.heap_fold.size = size;
    return osprey_intern_var(ctx, kind, &payload);
}

static uint32_t heap_fold_variable_id(const OspreyContext *ctx, uint8_t kind,
                                      OspreyRegionId region_id,
                                      uint64_t size)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.heap_fold.region = region_id;
    payload.heap_fold.size = size;
    return variable_id(ctx, kind, &payload);
}

static OspreyInternResult seed_homo(OspreyContext *ctx, OspreyAddress first,
                                    OspreyAddress second, int64_t size)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.segment.a1 = first;
    payload.segment.a2 = second;
    payload.segment.size = size;
    return osprey_intern_var(ctx, OSPREY_PRED_HOMO_SEGMENT, &payload);
}

static uint32_t homo_variable_id(const OspreyContext *ctx,
                                 OspreyAddress first,
                                 OspreyAddress second, int64_t size)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.segment.a1 = first;
    payload.segment.a2 = second;
    payload.segment.size = size;
    return variable_id(ctx, OSPREY_PRED_HOMO_SEGMENT, &payload);
}

static OspreyInternResult seed_field(OspreyContext *ctx, OspreyChunk value,
                                     OspreyAddress base)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.attached.chunk = value;
    payload.attached.base = base;
    return osprey_intern_var(ctx, OSPREY_PRED_FIELD_OF, &payload);
}

static OspreyInternResult seed_primitive(OspreyContext *ctx,
                                         OspreyChunk value)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.chunk = value;
    return osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &payload);
}

static OspreyInternResult seed_heap_foldable(OspreyContext *ctx,
                                             OspreyRegionId region_id,
                                             uint64_t size)
{
    return seed_heap_fold(ctx, OSPREY_PRED_FOLDABLE_HEAP, region_id, size);
}

static OspreyInternResult seed_heap_unfoldable(OspreyContext *ctx,
                                               OspreyRegionId region_id,
                                               uint64_t size)
{
    return seed_heap_fold(ctx, OSPREY_PRED_UNFOLDABLE_HEAP, region_id, size);
}

static OspreyInternResult seed_array(OspreyContext *ctx,
                                    OspreyRegionId region_id, int64_t lo,
                                    int64_t hi, int64_t stride)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.segment.a1 = address(region_id, lo);
    payload.segment.a2 = address(region_id, hi);
    payload.segment.size = stride;
    return osprey_intern_var(ctx, OSPREY_PRED_ARRAY, &payload);
}

static OspreyInternResult seed_scalar(OspreyContext *ctx,
                                     const OspreyChunk *value)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.chunk = *value;
    return osprey_intern_var(ctx, OSPREY_PRED_SCALAR, &payload);
}

static OspreyInternResult seed_array_start(OspreyContext *ctx,
                                           const OspreyAddress *value)
{
    OspreyVarPayload payload;
    memset(&payload, 0, sizeof(payload));
    payload.addr = *value;
    return osprey_intern_var(ctx, OSPREY_PRED_ARRAY_START, &payload);
}

static const OspreyVar *find_array(const OspreyContext *ctx,
                                   OspreyRegionId region_id, int64_t lo,
                                   int64_t hi, int64_t stride)
{
    for (guint i = 0; i < ctx->graph->vars->len; i++) {
        const OspreyVar *variable = &g_array_index(ctx->graph->vars,
                                                    OspreyVar, i);
        if (variable->kind == OSPREY_PRED_ARRAY &&
            variable->payload.segment.a1.region.kind == region_id.kind &&
            variable->payload.segment.a1.region.code_image_id ==
                region_id.code_image_id &&
            variable->payload.segment.a1.region.site_offset ==
                region_id.site_offset &&
            variable->payload.segment.a1.offset == lo &&
            variable->payload.segment.a2.offset == hi &&
            variable->payload.segment.size == stride) {
            return variable;
        }
    }
    return NULL;
}

static char *graph_dump(const OspreyContext *ctx)
{
    FILE *stream = tmpfile();
    CHECK(stream != NULL, "temporary canonical graph dump file");
    if (stream == NULL) return g_strdup("");
    CHECK(osprey_graph_dump_file(ctx, stream),
          "canonical graph dump succeeds");
    fflush(stream);
    fseek(stream, 0, SEEK_END);
    long length = ftell(stream);
    CHECK(length >= 0, "canonical graph dump length");
    rewind(stream);
    size_t size = length < 0 ? 0 : (size_t)length;
    char *text = g_malloc(size + 1);
    size_t actual = fread(text, 1, size, stream);
    text[actual] = '\0';
    fclose(stream);
    return text;
}

static char *cb03_dump(bool reverse)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk extent = chunk(global, 0, 24);
    add_extent(ctx, &extent);
    if (reverse) {
        seed_array(ctx, global, 8, 24, 8);
        seed_array(ctx, global, 0, 16, 8);
    } else {
        seed_array(ctx, global, 0, 16, 8);
        seed_array(ctx, global, 8, 24, 8);
    }
    CHECK(build_secondary(ctx), "CB03 permutation build");
    char *text = graph_dump(ctx);
    osprey_free(ctx);
    return text;
}

static void test_ca01(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk value = chunk(global, 0, 8);
    add_logical(ctx, 0x10, &value, 3, 1);
    CHECK(build_base(ctx), "CA01 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CA01) == 1,
          "CA01 emits one logical prior");
    const OspreyFactor *factor = first_rule(ctx, OSPREY_RULE_CA01);
    CHECK(factor != NULL && fabs(factor->p - 0.25) < 1e-12,
          "CA01 uses logical sample support");
    uint32_t primitive = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                           &value);
    uint32_t ids[1] = { primitive };
    expect_factor(ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_PRIOR, false, 0.25, 0, ids, 1,
                  "CA01 exact primitive prior");
    const FactorExpectation ca01_block[] = {
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_PRIOR, false, 0.25,
          0, ids, 1 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CA01, ca01_block,
                        G_N_ELEMENTS(ca01_block),
                        "CA01 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CA01, 1,
                               "CA01 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CA01, 1, 3, 0,
                                "CA01 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    CHECK(build_base(ctx), "CA01 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CA01) == 0,
          "CA01 has no witness without Access");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &value, 2, 1);
    add_logical(ctx, 0x10, &value, 1, 1);
    CHECK(build_base(ctx), "CA01 duplicate RMW projection");
    CHECK(rule_count(ctx, OSPREY_RULE_CA01) == 1,
          "CA01 merges duplicate logical load/store rows");
    CHECK(chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &value) !=
              UINT32_MAX,
          "CA01 retains one primitive for duplicate rows");
    factor = first_rule(ctx, OSPREY_RULE_CA01);
    CHECK(factor != NULL && probability_bits_equal(factor->p, 0.5),
          "CA01 duplicate rows merge logical support");
    osprey_free(ctx);

    ctx = new_context();
    ctx->total_samples = 0;
    add_logical(ctx, 0x10, &value, 1, 1);
    CHECK(osprey_stage3_base(ctx) == OSPREY_INVALID_GRAPH,
          "CA01 rejects a zero sample denominator");
    osprey_free(ctx);
}

static void test_ca02(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk a = chunk(global, 0, 8);
    OspreyChunk b = chunk(global, 8, 8);
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x20, &b, 1, 1);
    CHECK(build_base(ctx), "CA02 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CA02) == 2,
          "CA02 preserves both directions");
    uint32_t first = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &a);
    uint32_t second = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &b);
    uint32_t forward[2] = { first, second };
    uint32_t reverse[2] = { second, first };
    expect_factor(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  forward, 2, "CA02 exact forward factor");
    expect_factor(ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  reverse, 2, "CA02 exact reverse factor");
    const FactorExpectation ca02_block[] = {
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, forward, 2 },
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, reverse, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CA02, ca02_block,
                        G_N_ELEMENTS(ca02_block),
                        "CA02 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CA02, 0,
                               "CA02 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CA02, 0, 6, 0,
                                "CA02 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical_value(ctx, 0x20, chunk(global, 17, 8), 1, 1);
    CHECK(build_base(ctx), "CA02 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CA02) == 0,
          "CA02 rejects a one-byte gap");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk narrow = chunk(global, 0, 4);
    OspreyChunk wide = chunk(global, 0, 8);
    add_logical(ctx, 0x10, &narrow, 1, 1);
    add_logical(ctx, 0x20, &wide, 1, 1);
    CHECK(build_base(ctx), "CA02 same-address widths");
    CHECK(rule_count(ctx, OSPREY_RULE_CA02) == 0 &&
          rule_count(ctx, OSPREY_RULE_CA03) == 2,
          "CA02/CA03 classify same-address widths as overlap");
    uint32_t narrow_id = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                            &narrow);
    uint32_t wide_id = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                         &wide);
    uint32_t overlap[2] = { narrow_id, wide_id };
    uint32_t reverse_overlap[2] = { wide_id, narrow_id };
    expect_factor(ctx, OSPREY_RULE_CA03, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  overlap, 2, "CA03 same-address forward overlap");
    expect_factor(ctx, OSPREY_RULE_CA03, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  reverse_overlap, 2, "CA03 same-address reverse overlap");
    osprey_free(ctx);

    ctx = new_context();
    OspreyRegionId stack = region(OSPREY_REGION_STACK_FUNCTION, 0);
    OspreyChunk other_region = chunk(stack, 8, 8);
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x20, &other_region, 1, 1);
    CHECK(build_base(ctx), "CA02 region mismatch");
    CHECK(rule_count(ctx, OSPREY_RULE_CA02) == 0 &&
          rule_count(ctx, OSPREY_RULE_CA03) == 0,
          "CA02/CA03 reject region mismatch");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk overflowing = chunk(global, INT64_MAX, 1);
    add_logical(ctx, 0x10, &overflowing, 1, 1);
    CHECK(osprey_stage3_base(ctx) == OSPREY_GRAPH_ARITHMETIC,
          "CA02 rejects an overflowing observed chunk endpoint");
    osprey_free(ctx);
}

static void test_ca03(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk a = chunk(global, 0, 16);
    OspreyChunk b = chunk(global, 8, 8);
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x20, &b, 1, 1);
    CHECK(build_base(ctx), "CA03 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CA03) == 2,
          "CA03 emits both negative directions");
    uint32_t first = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &a);
    uint32_t second = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &b);
    uint32_t forward[2] = { first, second };
    uint32_t reverse[2] = { second, first };
    expect_factor(ctx, OSPREY_RULE_CA03, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  forward, 2, "CA03 exact forward factor");
    expect_factor(ctx, OSPREY_RULE_CA03, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  reverse, 2, "CA03 exact reverse factor");
    const FactorExpectation ca03_block[] = {
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, forward, 2 },
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, reverse, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CA03, ca03_block,
                        G_N_ELEMENTS(ca03_block),
                        "CA03 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CA03, 0,
                               "CA03 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CA03, 0, 6, 0,
                                "CA03 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk overlap_low = chunk(global, 0, 8);
    OspreyChunk overlap_high = chunk(global, 4, 16);
    add_logical(ctx, 0x20, &overlap_high, 1, 1);
    add_logical(ctx, 0x10, &overlap_low, 1, 1);
    CHECK(build_base(ctx), "CA03 reverse-direction overlap");
    CHECK(rule_count(ctx, OSPREY_RULE_CA03) == 2,
          "CA03 emits both directions for reverse overlap geometry");
    uint32_t overlap_low_id = chunk_variable_id(ctx,
                                                 OSPREY_PRED_PRIMITIVE_VAR,
                                                 &overlap_low);
    uint32_t overlap_high_id = chunk_variable_id(ctx,
                                                  OSPREY_PRED_PRIMITIVE_VAR,
                                                  &overlap_high);
    uint32_t overlap_forward[2] = { overlap_high_id, overlap_low_id };
    uint32_t overlap_reverse[2] = { overlap_low_id, overlap_high_id };
    const FactorExpectation ca03_reverse_block[] = {
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, overlap_forward, 2 },
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, overlap_reverse, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CA03, ca03_reverse_block,
                        G_N_ELEMENTS(ca03_reverse_block),
                        "CA03 reverse overlap factor block");
    osprey_free(ctx);

    ctx = new_context();
    add_logical_value(ctx, 0x10, chunk(global, 0, 8), 1, 1);
    add_logical_value(ctx, 0x20, chunk(global, 8, 8), 1, 1);
    CHECK(build_base(ctx), "CA03 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CA03) == 0,
          "CA03 rejects exact adjacency");
    osprey_free(ctx);
}

static void test_ca04(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk value = chunk(global, 0, 8);
    add_logical(ctx, 0x10, &value, 1, 1);
    CHECK(build_base(ctx), "CA04 positive");
    const OspreyFactor *factor = first_rule(ctx, OSPREY_RULE_CA04);
    CHECK(factor != NULL && factor->head_idx == 1 && factor->num_vars == 2,
          "CA04 keeps antecedent then head order");
    CHECK(rule_count(ctx, OSPREY_RULE_CA04) == 1,
          "CA04 emits one primitive-access edge");
    uint32_t primitive = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                           &value);
    uint32_t access = access_variable_id(ctx, 0x10, &value);
    uint32_t ids[2] = { primitive, access };
    expect_factor(ctx, OSPREY_RULE_CA04, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  ids, 2, "CA04 exact antecedent and head");
    const FactorExpectation ca04_block[] = {
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, ids, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CA04, ca04_block,
                        G_N_ELEMENTS(ca04_block),
                        "CA04 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CA04, 1,
                               "CA04 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CA04, 1, 3, 0,
                                "CA04 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    CHECK(build_base(ctx), "CA04 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CA04) == 0,
          "CA04 has no edge without Access");
    osprey_free(ctx);
}

static void test_ca05(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk a = chunk(global, 0, 8);
    OspreyChunk b = chunk(global, 16, 8);
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x10, &b, 1, 1);
    CHECK(build_base(ctx), "CA05 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CA05) == 4,
          "CA05 performs complete P02 by R01 join");
    uint32_t primitive_a = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                             &a);
    uint32_t primitive_b = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                             &b);
    uint32_t access_a = access_variable_id(ctx, 0x10, &a);
    uint32_t access_b = access_variable_id(ctx, 0x10, &b);
    uint32_t ids[2] = { access_a, primitive_a };
    expect_factor(ctx, OSPREY_RULE_CA05, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  ids, 2, "CA05 exact first self join");
    ids[0] = access_b;
    expect_factor(ctx, OSPREY_RULE_CA05, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  ids, 2, "CA05 exact second-to-first join");
    ids[1] = primitive_b;
    expect_factor(ctx, OSPREY_RULE_CA05, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  ids, 2, "CA05 exact second self join");
    ids[0] = access_a;
    expect_factor(ctx, OSPREY_RULE_CA05, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  ids, 2, "CA05 exact first-to-second join");
    uint32_t ca05_first_self[2] = { access_a, primitive_a };
    uint32_t ca05_second_first[2] = { access_b, primitive_a };
    uint32_t ca05_second_self[2] = { access_b, primitive_b };
    uint32_t ca05_first_second[2] = { access_a, primitive_b };
    const FactorExpectation ca05_block[] = {
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, ca05_first_self, 2 },
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, ca05_second_first, 2 },
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, ca05_second_self, 2 },
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, ca05_first_second, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CA05, ca05_block,
                        G_N_ELEMENTS(ca05_block),
                        "CA05 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CA05, 0,
                               "CA05 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CA05, 0, 7, 0,
                                "CA05 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    OspreyRegionId stack = region(OSPREY_REGION_STACK_FUNCTION, 1);
    OspreyChunk c = chunk(stack, 0, 8);
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x10, &b, 1, 1);
    add_logical(ctx, 0x10, &c, 1, 1);
    CHECK(build_base(ctx), "CA05 three-chunk cross-region join");
    CHECK(rule_count(ctx, OSPREY_RULE_CA04) == 3 &&
          rule_count(ctx, OSPREY_RULE_CA05) == 9,
          "CA05 joins every P02 with every same-PC chunk");
    OspreyChunk chunks[3] = { a, b, c };
    for (guint source = 0; source < G_N_ELEMENTS(chunks); source++) {
        uint32_t source_access = access_variable_id(ctx, 0x10,
                                                    &chunks[source]);
        for (guint target = 0; target < G_N_ELEMENTS(chunks); target++) {
            uint32_t target_primitive = chunk_variable_id(
                ctx, OSPREY_PRED_PRIMITIVE_VAR, &chunks[target]);
            uint32_t ids[2] = { source_access, target_primitive };
            expect_factor(ctx, OSPREY_RULE_CA05, OSPREY_GRAPH_BASE_CA,
                          OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                          ids, 2, "CA05 exact cross-region join");
        }
    }
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x20, &b, 1, 1);
    CHECK(build_base(ctx), "CA05 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CA05) == 2,
          "CA05 joins only same-instruction accesses");
    osprey_free(ctx);
}

static void test_ca06(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk value = chunk(global, 0, 8);
    add_logical(ctx, 0x10, &value, 1, 2);
    CHECK(build_base(ctx), "CA06 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CA06) == 1,
          "CA06 emits a scalar implication");
    const OspreyFactor *factor = first_rule(ctx, OSPREY_RULE_CA06);
    CHECK(factor != NULL && fabs(factor->p - 0.5) < 1e-12,
          "CA06 uses logical support");
    uint32_t access = access_variable_id(ctx, 0x10, &value);
    uint32_t scalar = chunk_variable_id(ctx, OSPREY_PRED_SCALAR, &value);
    uint32_t ids[2] = { access, scalar };
    expect_factor(ctx, OSPREY_RULE_CA06, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.5, 1,
                  ids, 2, "CA06 exact access-to-scalar factor");
    const FactorExpectation ca06_block[] = {
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.5,
          1, ids, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CA06, ca06_block,
                        G_N_ELEMENTS(ca06_block),
                        "CA06 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CA06, 1,
                               "CA06 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CA06, 1, 3, 0,
                                "CA06 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &value, 1, 1);
    add_logical(ctx, 0x10, &value, 1, 1);
    CHECK(build_base(ctx), "CA06 duplicate fact rows");
    CHECK(rule_count(ctx, OSPREY_RULE_CA06) == 1 &&
          chunk_variable_id(ctx, OSPREY_PRED_SCALAR, &value) != UINT32_MAX,
          "CA06 counts one distinct logical chunk");
    factor = first_rule(ctx, OSPREY_RULE_CA06);
    CHECK(factor != NULL && probability_bits_equal(factor->p, 0.5),
          "CA06 duplicate rows retain merged support");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &value, 1, 1);
    add_logical_value(ctx, 0x10, chunk(global, 8, 8), 1, 1);
    CHECK(build_base(ctx), "CA06 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CA06) == 0,
          "CA06 rejects a multi-chunk instruction group");
    osprey_free(ctx);
}

static void test_ca07(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk a = chunk(global, 8, 8);
    OspreyChunk b = chunk(global, 0, 8);
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x20, &b, 1, 3);
    CHECK(build_base(ctx), "CA07 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CA07) == 2,
          "CA07 accepts adjacency in either address direction");
    const OspreyFactor *factor = first_rule(ctx, OSPREY_RULE_CA07);
    CHECK(factor != NULL && fabs(factor->p - 0.2) < 1e-12,
          "CA07 applies the lower clamp");
    uint32_t first = chunk_variable_id(ctx, OSPREY_PRED_SCALAR, &a);
    uint32_t second = chunk_variable_id(ctx, OSPREY_PRED_SCALAR, &b);
    uint32_t forward[2] = { first, second };
    uint32_t reverse[2] = { second, first };
    expect_factor(ctx, OSPREY_RULE_CA07, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.2, 1,
                  forward, 2, "CA07 exact lower-clamp forward factor");
    expect_factor(ctx, OSPREY_RULE_CA07, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.2, 1,
                  reverse, 2, "CA07 exact lower-clamp reverse factor");
    const FactorExpectation ca07_lower_block[] = {
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.2,
          1, forward, 2 },
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.2,
          1, reverse, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CA07, ca07_lower_block,
                        G_N_ELEMENTS(ca07_lower_block),
                        "CA07 complete lower-clamp factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CA07, 0,
                               "CA07 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CA07, 0, 6, 0,
                                "CA07 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 4);
    add_logical(ctx, 0x20, &b, 1, 4);
    CHECK(build_base(ctx), "CA07 upper clamp");
    CHECK(rule_count(ctx, OSPREY_RULE_CA07) == 2,
          "CA07 emits both upper-clamp directions");
    first = chunk_variable_id(ctx, OSPREY_PRED_SCALAR, &a);
    second = chunk_variable_id(ctx, OSPREY_PRED_SCALAR, &b);
    forward[0] = first;
    forward[1] = second;
    reverse[0] = second;
    reverse[1] = first;
    expect_factor(ctx, OSPREY_RULE_CA07, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  forward, 2, "CA07 exact upper-clamp forward factor");
    expect_factor(ctx, OSPREY_RULE_CA07, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  reverse, 2, "CA07 exact upper-clamp reverse factor");
    const FactorExpectation ca07_upper_block[] = {
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, forward, 2 },
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, reverse, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CA07, ca07_upper_block,
                        G_N_ELEMENTS(ca07_upper_block),
                        "CA07 complete upper-clamp factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CA07, 0,
                               "CA07 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CA07, 0, 6, 0,
                                "CA07 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 5);
    add_logical(ctx, 0x20, &b, 1, 4);
    CHECK(build_base(ctx), "CA07 unequal upper-clamp supports");
    CHECK(rule_count(ctx, OSPREY_RULE_CA07) == 2,
          "CA07 clamps unequal saturated supports at the upper bound");
    factor = first_rule(ctx, OSPREY_RULE_CA07);
    CHECK(factor != NULL && probability_bits_equal(factor->p, 0.8),
          "CA07 uses the upper clamp after support saturation");
    first = chunk_variable_id(ctx, OSPREY_PRED_SCALAR, &a);
    second = chunk_variable_id(ctx, OSPREY_PRED_SCALAR, &b);
    uint32_t ca07_saturated_forward[2] = { first, second };
    uint32_t ca07_saturated_reverse[2] = { second, first };
    const FactorExpectation ca07_saturated_block[] = {
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, ca07_saturated_forward, 2 },
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, ca07_saturated_reverse, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CA07, ca07_saturated_block,
                        G_N_ELEMENTS(ca07_saturated_block),
                        "CA07 complete unequal-saturated factor block");
    expect_candidate_accounting(ctx, OSPREY_RULE_CA07, 0, 6, 0,
                                "CA07 unequal proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 2);
    add_logical(ctx, 0x20, &b, 1, 3);
    CHECK(build_base(ctx), "CA07 unequal interior supports");
    CHECK(rule_count(ctx, OSPREY_RULE_CA07) == 2,
          "CA07 retains unequal non-clamped support");
    factor = first_rule(ctx, OSPREY_RULE_CA07);
    CHECK(factor != NULL && fabs(factor->p - 0.3) < 1e-12,
          "CA07 applies the exact unequal-support formula");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x10, &b, 1, 1);
    CHECK(build_base(ctx), "CA07 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CA07) == 0,
          "CA07 requires distinct instructions");
    osprey_free(ctx);
}

static void test_ca08(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk value = chunk(global, 8, 8);
    add_logical(ctx, 0x10, &value, 1, 1);
    OspreyVarPayload field;
    memset(&field, 0, sizeof(field));
    field.attached.chunk = value;
    field.attached.base = address(global, 8);
    CHECK(osprey_intern_var(ctx, OSPREY_PRED_FIELD_OF, &field).inserted,
          "CA08 seeded field candidate");
    CHECK(build_base(ctx), "CA08 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CA08) == 2,
          "CA08 preserves both negative directions");
    uint32_t scalar = chunk_variable_id(ctx, OSPREY_PRED_SCALAR, &value);
    uint32_t field_id = field_variable_id(ctx, &value, &value.address);
    uint32_t forward[2] = { scalar, field_id };
    uint32_t reverse[2] = { field_id, scalar };
    expect_factor(ctx, OSPREY_RULE_CA08, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  forward, 2, "CA08 exact scalar-to-field factor");
    expect_factor(ctx, OSPREY_RULE_CA08, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  reverse, 2, "CA08 exact field-to-scalar factor");
    const FactorExpectation ca08_single_block[] = {
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, forward, 2 },
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, reverse, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CA08, ca08_single_block,
                        G_N_ELEMENTS(ca08_single_block),
                        "CA08 complete single-base factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CA08, 0,
                               "CA08 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CA08, 0, 3, 0,
                                "CA08 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &value, 1, 1);
    OspreyChunk full_extent = chunk(global, 0, 16);
    add_extent(ctx, &full_extent);
    OspreyAddress base_zero = address(global, 0);
    OspreyAddress base_eight = address(global, 8);
    OspreyVarPayload first_field;
    OspreyVarPayload second_field;
    memset(&first_field, 0, sizeof(first_field));
    memset(&second_field, 0, sizeof(second_field));
    first_field.attached.chunk = value;
    first_field.attached.base = base_zero;
    second_field.attached.chunk = value;
    second_field.attached.base = base_eight;
    CHECK(osprey_intern_var(ctx, OSPREY_PRED_FIELD_OF,
                            &first_field).inserted,
          "CA08 first field base");
    CHECK(osprey_intern_var(ctx, OSPREY_PRED_FIELD_OF,
                            &second_field).inserted,
          "CA08 second field base");
    CHECK(build_base(ctx), "CA08 multiple bases");
    CHECK(rule_count(ctx, OSPREY_RULE_CA08) == 4,
          "CA08 retains both field-base candidates");
    uint32_t scalar_id = chunk_variable_id(ctx, OSPREY_PRED_SCALAR, &value);
    uint32_t first_field_id = field_variable_id(ctx, &value, &base_zero);
    uint32_t second_field_id = field_variable_id(ctx, &value, &base_eight);
    uint32_t pair[2] = { scalar_id, first_field_id };
    uint32_t reverse_pair[2] = { first_field_id, scalar_id };
    expect_factor(ctx, OSPREY_RULE_CA08, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  pair, 2, "CA08 first-base scalar direction");
    expect_factor(ctx, OSPREY_RULE_CA08, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  reverse_pair, 2, "CA08 first-base reverse direction");
    pair[1] = second_field_id;
    reverse_pair[0] = second_field_id;
    expect_factor(ctx, OSPREY_RULE_CA08, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  pair, 2, "CA08 second-base scalar direction");
    expect_factor(ctx, OSPREY_RULE_CA08, OSPREY_GRAPH_BASE_CA,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  reverse_pair, 2, "CA08 second-base reverse direction");
    uint32_t ca08_first_forward[2] = { scalar_id, first_field_id };
    uint32_t ca08_first_reverse[2] = { first_field_id, scalar_id };
    uint32_t ca08_second_forward[2] = { scalar_id, second_field_id };
    uint32_t ca08_second_reverse[2] = { second_field_id, scalar_id };
    const FactorExpectation ca08_multi_block[] = {
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, ca08_first_forward, 2 },
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, ca08_first_reverse, 2 },
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, ca08_second_forward, 2 },
        { OSPREY_GRAPH_BASE_CA, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, ca08_second_reverse, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CA08, ca08_multi_block,
                        G_N_ELEMENTS(ca08_multi_block),
                        "CA08 complete multi-base factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CA08, 0,
                               "CA08 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CA08, 0, 3, 0,
                                "CA08 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &value, 1, 1);
    CHECK(build_base(ctx), "CA08 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CA08) == 0,
          "CA08 does not invent field bases");
    osprey_free(ctx);
}

static void test_cb01(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk a = chunk(global, 0, 8);
    OspreyChunk b = chunk(global, 8, 8);
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x20, &b, 1, 1);
    OspreyMayArrayFact fact;
    memset(&fact, 0, sizeof(fact));
    fact.start = a.address;
    fact.element_count = 2;
    fact.element_size = 8;
    fact.evidence_kind = OSPREY_MAY_ARRAY_CALLOC_GEOMETRY;
    fact.sample_support = 1;
    g_array_append_val(ctx->mayarray_facts, fact);
    CHECK(build_secondary(ctx), "CB01 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CB01) == 2,
          "CB01 emits independent head priors");
    OspreyAddress start_address = a.address;
    uint32_t array = array_variable_id(ctx, global, 0, 16, 8);
    uint32_t start = start_variable_id(ctx, &start_address);
    uint32_t array_ids[1] = { array };
    uint32_t start_ids[1] = { start };
    expect_factor(ctx, OSPREY_RULE_CB01, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_PRIOR, false, 0.8, 0,
                  array_ids, 1, "CB01 exact array prior");
    expect_factor(ctx, OSPREY_RULE_CB01, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_PRIOR, false, 0.8, 0,
                  start_ids, 1, "CB01 exact array-start prior");
    const FactorExpectation cb01_block[] = {
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_PRIOR, false, 0.8,
          0, array_ids, 1 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_PRIOR, false, 0.8,
          0, start_ids, 1 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CB01, cb01_block,
                        G_N_ELEMENTS(cb01_block),
                        "CB01 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CB01, 2,
                               "CB01 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CB01, 2, 10, 0,
                                "CB01 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    fact.element_count = 0;
    g_array_append_val(ctx->mayarray_facts, fact);
    CHECK(osprey_stage3_base(ctx) == OSPREY_INVALID_GRAPH,
          "CB01 rejects zero geometry as malformed graph input");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    fact.element_count = 2;
    fact.element_size = 0;
    g_array_append_val(ctx->mayarray_facts, fact);
    CHECK(osprey_stage3_base(ctx) == OSPREY_INVALID_GRAPH,
          "CB01 rejects zero element size as malformed graph input");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    fact.element_count = UINT64_MAX;
    fact.element_size = 2;
    g_array_append_val(ctx->mayarray_facts, fact);
    CHECK(osprey_stage3_base(ctx) == OSPREY_GRAPH_ARITHMETIC,
          "CB01 rejects product overflow");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    fact.element_count = 1;
    fact.element_size = 1;
    fact.start.offset = INT64_MAX;
    g_array_append_val(ctx->mayarray_facts, fact);
    CHECK(osprey_stage3_base(ctx) == OSPREY_GRAPH_ARITHMETIC,
          "CB01 rejects endpoint overflow");
    osprey_free(ctx);

    ctx = new_context();
    OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x44);
    OspreyMayArrayFact heap_array;
    memset(&heap_array, 0, sizeof(heap_array));
    heap_array.start = address(heap, 0);
    heap_array.element_count = 2;
    heap_array.element_size = 8;
    heap_array.evidence_kind = OSPREY_MAY_ARRAY_CALLOC_GEOMETRY;
    heap_array.sample_support = 1;
    OspreyMallocFact allocation;
    memset(&allocation, 0, sizeof(allocation));
    allocation.site_pc = heap.site_offset;
    allocation.requested_size = 8;
    allocation.sample_support = 1;
    g_array_append_val(ctx->mayarray_facts, heap_array);
    g_array_append_val(ctx->alloc_facts, allocation);
    CHECK(osprey_stage3_base(ctx) == OSPREY_INVALID_GRAPH,
          "CB01 rejects F06/F05 size contradiction as invalid graph input");
    osprey_free(ctx);

    ctx = new_context();
    heap_array.start = address(heap, 0);
    heap_array.element_count = 2;
    heap_array.element_size = 8;
    allocation.site_pc = heap.site_offset + 1;
    allocation.requested_size = 16;
    g_array_append_val(ctx->mayarray_facts, heap_array);
    g_array_append_val(ctx->alloc_facts, allocation);
    CHECK(osprey_stage3_base(ctx) == OSPREY_INVALID_GRAPH,
          "CB01 rejects F06/F05 site contradiction as invalid graph input");
    osprey_free(ctx);
}

static void test_cb02(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk low = chunk(global, 0, 8);
    OspreyChunk high = chunk(global, 16, 4);
    add_logical(ctx, 0x10, &low, 1, 1);
    add_logical(ctx, 0x10, &high, 1, 1);
    CHECK(build_secondary(ctx), "CB02 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CB02) == 1,
          "CB02 emits one complete extrema implication");
    bool found_end = false;
    for (guint i = 0; i < ctx->graph->vars->len; i++) {
        const OspreyVar *variable = &g_array_index(ctx->graph->vars,
                                                    OspreyVar, i);
        if (variable->kind == OSPREY_PRED_ARRAY &&
            variable->payload.segment.a1.offset == 0 &&
            variable->payload.segment.a2.offset == 20 &&
            variable->payload.segment.size == 8) {
            found_end = true;
        }
    }
    CHECK(found_end, "CB02 adds the high chunk width to hi");
    uint32_t low_access = access_variable_id(ctx, 0x10, &low);
    uint32_t high_access = access_variable_id(ctx, 0x10, &high);
    uint32_t array = array_variable_id(ctx, global, 0, 20, 8);
    uint32_t ids[3] = { low_access, high_access, array };
    expect_factor(ctx, OSPREY_RULE_CB02, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 2,
                  ids, 3, "CB02 exact low-high-array implication");
    const FactorExpectation cb02_block[] = {
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          2, ids, 3 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CB02, cb02_block,
                        G_N_ELEMENTS(cb02_block),
                        "CB02 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CB02, 1,
                               "CB02 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CB02, 1, 7, 0,
                                "CB02 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &low, 1, 1);
    add_logical_value(ctx, 0x10, chunk(global, 4, 3), 1, 1);
    CHECK(build_secondary(ctx), "CB02 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CB02) == 0,
          "CB02 rejects a span shorter than its stride");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk narrow = chunk(global, 0, 4);
    OspreyChunk wide = chunk(global, 0, 8);
    add_logical(ctx, 0x10, &narrow, 1, 1);
    add_logical(ctx, 0x10, &wide, 1, 1);
    CHECK(build_secondary(ctx), "CB02 same-address widths");
    CHECK(rule_count(ctx, OSPREY_RULE_CB02) == 1,
          "CB02 omits duplicate roles and keeps the cross-width witness");
    const OspreyFactor *factor = first_rule(ctx, OSPREY_RULE_CB02);
    CHECK(factor != NULL && factor->num_vars == 3 &&
          factor->var_ids[0] != factor->var_ids[1],
          "CB02 factor has two distinct extrema antecedents");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk middle = chunk(global, 8, 2);
    low = chunk(global, 0, 4);
    high = chunk(global, 16, 8);
    add_logical(ctx, 0x10, &high, 1, 1);
    add_logical(ctx, 0x10, &middle, 1, 1);
    add_logical(ctx, 0x10, &low, 1, 1);
    add_logical(ctx, 0x10, &low, 1, 1);
    CHECK(build_secondary(ctx), "CB02 three-chunk extrema");
    CHECK(rule_count(ctx, OSPREY_RULE_CB02) == 1,
          "CB02 ignores middle and duplicate logical chunks");
    uint32_t low_id = access_variable_id(ctx, 0x10, &low);
    uint32_t high_id = access_variable_id(ctx, 0x10, &high);
    uint32_t array_id = array_variable_id(ctx, global, 0, 24, 4);
    uint32_t extrema[3] = { low_id, high_id, array_id };
    expect_factor(ctx, OSPREY_RULE_CB02, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 2,
                  extrema, 3, "CB02 exact three-chunk extrema factor");
    CHECK(!factor_exact(ctx, OSPREY_RULE_CB02, OSPREY_GRAPH_SECONDARY,
                        OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 2,
                        (uint32_t[3]){ low_id,
                                       access_variable_id(ctx, 0x10, &middle),
                                       array_id }, 3),
          "CB02 excludes the middle chunk from extrema antecedents");
    osprey_free(ctx);
}

static void test_cb03(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk a = chunk(global, 0, 8);
    OspreyChunk b = chunk(global, 16, 8);
    add_extent(ctx, &a);
    add_extent(ctx, &b);
    CHECK(seed_array(ctx, global, 0, 16, 8).inserted,
          "CB03 first seed");
    CHECK(seed_array(ctx, global, 8, 24, 8).inserted,
          "CB03 second seed");
    CHECK(build_secondary(ctx), "CB03 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CB03) == 7,
          "CB03 emits two directions and the union implication");
    const OspreyVar *union_array = find_array(ctx, global, 0, 24, 8);
    CHECK(union_array != NULL && union_array->direct_support == 1,
          "CB03 counts its derivation witness once across closure rounds");
    uint32_t first = array_variable_id(ctx, global, 0, 16, 8);
    uint32_t second = array_variable_id(ctx, global, 8, 24, 8);
    uint32_t union_id = array_variable_id(ctx, global, 0, 24, 8);
    uint32_t first_second[2] = { first, second };
    uint32_t second_first[2] = { second, first };
    uint32_t first_union[2] = { first, union_id };
    uint32_t union_first[2] = { union_id, first };
    uint32_t union_second[2] = { union_id, second };
    uint32_t second_union[2] = { second, union_id };
    uint32_t conjunction[3] = { first, second, union_id };
    expect_factor(ctx, OSPREY_RULE_CB03, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  first_second, 2, "CB03 exact first-to-second factor");
    expect_factor(ctx, OSPREY_RULE_CB03, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  second_first, 2, "CB03 exact second-to-first factor");
    expect_factor(ctx, OSPREY_RULE_CB03, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 2,
                  conjunction, 3, "CB03 exact union implication");
    expect_factor(ctx, OSPREY_RULE_CB03, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  first_union, 2, "CB03 exact first-union factor");
    expect_factor(ctx, OSPREY_RULE_CB03, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  union_first, 2, "CB03 exact union-first factor");
    expect_factor(ctx, OSPREY_RULE_CB03, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  union_second, 2, "CB03 exact union-second factor");
    expect_factor(ctx, OSPREY_RULE_CB03, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  second_union, 2, "CB03 exact second-union factor");
    const FactorExpectation cb03_block[] = {
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, first_second, 2 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, second_first, 2 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          2, conjunction, 3 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, first_union, 2 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, union_first, 2 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, union_second, 2 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, second_union, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CB03, cb03_block,
                        G_N_ELEMENTS(cb03_block),
                        "CB03 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CB03, 1,
                               "CB03 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CB03, 1, 1, 0,
                                "CB03 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_extent(ctx, &a);
    OspreyChunk near_b = chunk(global, 17, 8);
    add_extent(ctx, &near_b);
    CHECK(seed_array(ctx, global, 0, 16, 8).inserted,
          "CB03 near first seed");
    CHECK(seed_array(ctx, global, 1, 16, 8).inserted,
          "CB03 near second seed");
    CHECK(build_secondary(ctx), "CB03 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CB03) == 0,
          "CB03 rejects unaligned starts");
    osprey_free(ctx);

    ctx = new_context();
    add_extent(ctx, &a);
    add_extent(ctx, &b);
    CHECK(seed_array(ctx, global, 0, 8, 8).inserted,
          "CB03 touching first seed");
    CHECK(seed_array(ctx, global, 8, 16, 8).inserted,
          "CB03 touching second seed");
    CHECK(build_secondary(ctx), "CB03 touching boundary");
    CHECK(rule_count(ctx, OSPREY_RULE_CB03) == 7 &&
          rule_count(ctx, OSPREY_RULE_CB04) == 0,
          "CB03 includes the printed a2.lo == a1.hi boundary");
    union_array = find_array(ctx, global, 0, 16, 8);
    CHECK(union_array != NULL && union_array->direct_support == 1,
          "CB03 touching union has one direct witness");
    osprey_free(ctx);

    char *forward = cb03_dump(false);
    char *reverse = cb03_dump(true);
    CHECK(strcmp(forward, reverse) == 0,
          "CB03 closure dump is independent of seed insertion order");
    g_free(reverse);
    g_free(forward);
}

static void test_cb04(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk a = chunk(global, 0, 8);
    OspreyChunk b = chunk(global, 16, 8);
    add_extent(ctx, &a);
    add_extent(ctx, &b);
    CHECK(seed_array(ctx, global, 0, 16, 8).inserted,
          "CB04 first seed");
    CHECK(seed_array(ctx, global, 8, 24, 4).inserted,
          "CB04 second seed");
    CHECK(build_secondary(ctx), "CB04 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CB04) == 8,
          "CB04 closes exclusions and two valid split supports");
    uint32_t first = array_variable_id(ctx, global, 0, 16, 8);
    uint32_t second = array_variable_id(ctx, global, 8, 24, 4);
    uint32_t left = array_variable_id(ctx, global, 0, 8, 8);
    uint32_t right = array_variable_id(ctx, global, 16, 24, 4);
    uint32_t ids[2] = { first, left };
    expect_factor(ctx, OSPREY_RULE_CB04, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  ids, 2, "CB04 exact left split support");
    ids[0] = second;
    ids[1] = right;
    expect_factor(ctx, OSPREY_RULE_CB04, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  ids, 2, "CB04 exact right split support");
    uint32_t pairs[][2] = {
        { left, second }, { second, left },
        { first, second }, { second, first },
        { first, right }, { right, first },
    };
    for (guint i = 0; i < G_N_ELEMENTS(pairs); i++) {
        expect_factor(ctx, OSPREY_RULE_CB04, OSPREY_GRAPH_SECONDARY,
                      OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                      pairs[i], 2, "CB04 exact exclusion direction");
    }
    const FactorExpectation cb04_block[] = {
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, (uint32_t[2]){ first, left }, 2 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, (uint32_t[2]){ second, right }, 2 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, pairs[0], 2 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, pairs[1], 2 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, pairs[2], 2 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, pairs[3], 2 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, pairs[4], 2 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, pairs[5], 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CB04, cb04_block,
                        G_N_ELEMENTS(cb04_block),
                        "CB04 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CB04, 2,
                               "CB04 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CB04, 2, 2, 0,
                                "CB04 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_extent(ctx, &a);
    add_extent(ctx, &b);
    CHECK(seed_array(ctx, global, 0, 8, 8).inserted,
          "CB04 near first seed");
    CHECK(seed_array(ctx, global, 4, 11, 4).inserted,
          "CB04 near second seed");
    CHECK(build_secondary(ctx), "CB04 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CB04) == 2,
          "CB04 keeps exclusion when both splits are too short");
    osprey_free(ctx);

    ctx = new_context();
    add_extent(ctx, &a);
    add_extent(ctx, &b);
    CHECK(seed_array(ctx, global, 0, 8, 8).inserted,
          "CB04 touching first seed");
    CHECK(seed_array(ctx, global, 8, 16, 4).inserted,
          "CB04 touching second seed");
    CHECK(build_secondary(ctx), "CB04 touching boundary");
    CHECK(rule_count(ctx, OSPREY_RULE_CB04) == 2,
          "CB04 includes incompatible arrays at the equality boundary");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk split_extent = chunk(global, 0, 16);
    add_extent(ctx, &split_extent);
    CHECK(seed_array(ctx, global, 0, 8, 8).inserted,
          "CB04 left-short first seed");
    CHECK(seed_array(ctx, global, 4, 16, 4).inserted,
          "CB04 left-short second seed");
    CHECK(build_secondary(ctx), "CB04 left split too short");
    CHECK(find_array(ctx, global, 8, 16, 4) != NULL,
          "CB04 retains a valid right split when left is short");
    CHECK(rule_count(ctx, OSPREY_RULE_CB04) >= 3,
          "CB04 emits the exclusion and valid right split support");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk right_split_extent = chunk(global, 0, 24);
    add_extent(ctx, &right_split_extent);
    CHECK(seed_array(ctx, global, 0, 16, 8).inserted,
          "CB04 right-short first seed");
    CHECK(seed_array(ctx, global, 8, 19, 4).inserted,
          "CB04 right-short second seed");
    CHECK(build_secondary(ctx), "CB04 right split too short");
    CHECK(find_array(ctx, global, 0, 8, 8) != NULL,
          "CB04 retains a valid left split when right is short");
    CHECK(rule_count(ctx, OSPREY_RULE_CB04) >= 3,
          "CB04 emits the exclusion and valid left split support");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk boundary = chunk(global, INT64_MAX - 16, 16);
    add_extent(ctx, &boundary);
    CHECK(seed_array(ctx, global, INT64_MAX - 16, INT64_MAX - 8, 8).inserted,
          "CB04 checked-boundary first seed");
    CHECK(seed_array(ctx, global, INT64_MAX - 12, INT64_MAX - 4, 4).inserted,
          "CB04 checked-boundary second seed");
    CHECK(build_secondary(ctx), "CB04 checked offset boundary");
    CHECK(find_array(ctx, global, INT64_MAX - 8, INT64_MAX - 4, 4) != NULL,
          "CB04 computes a boundary-safe right split");
    osprey_free(ctx);
}

static void test_cb05(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk scalar = chunk(global, 8, 8);
    OspreyChunk extent = chunk(global, 0, 32);
    add_extent(ctx, &extent);
    CHECK(seed_array(ctx, global, 0, 32, 8).inserted,
          "CB05 array seed");
    CHECK(seed_scalar(ctx, &scalar).inserted,
          "CB05 scalar seed");
    CHECK(build_secondary(ctx), "CB05 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CB05) == 4,
          "CB05 emits exclusion and two residual supports");
    uint32_t array = array_variable_id(ctx, global, 0, 32, 8);
    uint32_t scalar_id = chunk_variable_id(ctx, OSPREY_PRED_SCALAR, &scalar);
    uint32_t left = array_variable_id(ctx, global, 0, 8, 8);
    uint32_t right = array_variable_id(ctx, global, 16, 32, 8);
    expect_factor(ctx, OSPREY_RULE_CB05, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 2,
                  (uint32_t[3]){ array, scalar_id, left }, 3,
                  "CB05 exact left residual support");
    expect_factor(ctx, OSPREY_RULE_CB05, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 2,
                  (uint32_t[3]){ array, scalar_id, right }, 3,
                  "CB05 exact right residual support");
    expect_factor(ctx, OSPREY_RULE_CB05, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  (uint32_t[2]){ scalar_id, array }, 2,
                  "CB05 exact scalar-to-array exclusion");
    expect_factor(ctx, OSPREY_RULE_CB05, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  (uint32_t[2]){ array, scalar_id }, 2,
                  "CB05 exact array-to-scalar exclusion");
    uint32_t cb05_left[3] = { array, scalar_id, left };
    uint32_t cb05_right[3] = { array, scalar_id, right };
    uint32_t cb05_scalar_exclusion[2] = { scalar_id, array };
    uint32_t cb05_array_exclusion[2] = { array, scalar_id };
    const FactorExpectation cb05_block[] = {
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          2, cb05_left, 3 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          2, cb05_right, 3 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, cb05_scalar_exclusion, 2 },
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, cb05_array_exclusion, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CB05, cb05_block,
                        G_N_ELEMENTS(cb05_block),
                        "CB05 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CB05, 2,
                               "CB05 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CB05, 2, 2, 0,
                                "CB05 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_extent(ctx, &extent);
    OspreyChunk outside = chunk(global, 32, 8);
    CHECK(seed_array(ctx, global, 0, 32, 8).inserted,
          "CB05 near array seed");
    CHECK(seed_scalar(ctx, &outside).inserted,
          "CB05 near scalar seed");
    CHECK(build_secondary(ctx), "CB05 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CB05) == 0,
          "CB05 excludes a scalar at the half-open hi");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk at_lo = chunk(global, 0, 8);
    add_extent(ctx, &extent);
    CHECK(seed_array(ctx, global, 0, 32, 8).inserted,
          "CB05 lo-boundary array");
    CHECK(seed_scalar(ctx, &at_lo).inserted,
          "CB05 lo-boundary scalar");
    CHECK(build_secondary(ctx), "CB05 scalar at lo");
    CHECK(rule_count(ctx, OSPREY_RULE_CB05) == 3,
          "CB05 keeps only the right residual at lo");
    CHECK(array_variable_id(ctx, global, 8, 32, 8) != UINT32_MAX,
          "CB05 creates the right residual at lo");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk before_hi = chunk(global, 24, 8);
    add_extent(ctx, &extent);
    CHECK(seed_array(ctx, global, 0, 32, 8).inserted,
          "CB05 before-hi array");
    CHECK(seed_scalar(ctx, &before_hi).inserted,
          "CB05 before-hi scalar");
    CHECK(build_secondary(ctx), "CB05 scalar immediately before hi");
    CHECK(rule_count(ctx, OSPREY_RULE_CB05) == 3,
          "CB05 keeps only the left residual before hi");
    CHECK(array_variable_id(ctx, global, 0, 24, 8) != UINT32_MAX,
          "CB05 creates the left residual before hi");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk crossing = chunk(global, 28, 8);
    OspreyChunk larger_extent = chunk(global, 0, 40);
    add_extent(ctx, &larger_extent);
    CHECK(seed_array(ctx, global, 0, 32, 8).inserted,
          "CB05 crossing array");
    CHECK(seed_scalar(ctx, &crossing).inserted,
          "CB05 crossing scalar");
    CHECK(build_secondary(ctx), "CB05 scalar crossing hi");
    CHECK(rule_count(ctx, OSPREY_RULE_CB05) == 3,
          "CB05 uses start containment for a crossing scalar");
    CHECK(array_variable_id(ctx, global, 0, 28, 8) != UINT32_MAX,
          "CB05 retains valid left residual when right split is absent");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk boundary_extent = chunk(global, INT64_MAX - 8, 8);
    OspreyChunk overflow_scalar = chunk(global, INT64_MAX - 3, 8);
    add_extent(ctx, &boundary_extent);
    CHECK(seed_array(ctx, global, INT64_MAX - 8, INT64_MAX, 8).inserted,
          "CB05 overflow array");
    CHECK(seed_scalar(ctx, &overflow_scalar).inserted,
          "CB05 overflow scalar");
    CHECK(build_base(ctx), "CB05 overflow base construction");
    CHECK(osprey_stage3_secondary(ctx) == OSPREY_GRAPH_ARITHMETIC,
          "CB05 reports overflowed scalar endpoint");
    CHECK(ctx->last_status == OSPREY_GRAPH_ARITHMETIC,
          "CB05 overflow status is arithmetic");
    osprey_free(ctx);
}

static void test_cb06(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    add_logical_value(ctx, 0x10, chunk(global, 0, 8), 1, 1);
    OspreyVar malformed;
    memset(&malformed, 0, sizeof(malformed));
    malformed.id = 0;
    malformed.kind = OSPREY_PRED_ARRAY;
    malformed.payload.segment.a1 = address(global, 0);
    malformed.payload.segment.a2 = address(global, 4);
    malformed.payload.segment.size = 8;
    g_array_set_size(ctx->graph->vars, 0);
    g_array_append_val(ctx->graph->vars, malformed);
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "CB06 relation setup");
    CHECK(osprey_stage3_secondary(ctx) == OSPREY_OK,
          "CB06 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CB06) == 1 &&
          g_array_index(ctx->graph->vars, OspreyVar, 0).hard_false,
          "CB06 emits exact hard-false factor");
    uint32_t malformed_id = 0;
    expect_factor(ctx, OSPREY_RULE_CB06, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_HARD_FALSE, false, 0.0,
                  UINT16_MAX, &malformed_id, 1,
                  "CB06 exact hard-false identity");
    const FactorExpectation cb06_block[] = {
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_HARD_FALSE, false, 0.0,
          UINT16_MAX, &malformed_id, 1 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CB06, cb06_block,
                        G_N_ELEMENTS(cb06_block),
                        "CB06 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CB06, 0,
                               "CB06 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CB06, 0, 0, 0,
                                "CB06 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_logical_value(ctx, 0x10, chunk(global, 0, 8), 1, 1);
    CHECK(seed_array(ctx, global, 0, 8, 8).inserted,
          "CB06 valid array");
    CHECK(build_secondary(ctx), "CB06 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CB06) == 0,
          "CB06 accepts one complete stride");
    osprey_free(ctx);

    ctx = new_context();
    malformed.payload.segment.a1 = address(global, 0);
    malformed.payload.segment.a2 = address(global, 8);
    malformed.payload.segment.size = 0;
    g_array_set_size(ctx->graph->vars, 0);
    g_array_append_val(ctx->graph->vars, malformed);
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "CB06 zero-stride relation setup");
    CHECK(osprey_stage3_secondary(ctx) == OSPREY_INVALID_GRAPH,
          "CB06 rejects a nonpositive injected stride");
    osprey_free(ctx);

    ctx = new_context();
    malformed.payload.segment.a1 = address(global, INT64_MIN);
    malformed.payload.segment.a2 = address(global, INT64_MAX);
    malformed.payload.segment.size = 8;
    g_array_set_size(ctx->graph->vars, 0);
    g_array_append_val(ctx->graph->vars, malformed);
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "CB06 overflow relation setup");
    CHECK(osprey_stage3_secondary(ctx) == OSPREY_GRAPH_ARITHMETIC,
          "CB06 rejects an unrepresentable injected span");
    osprey_free(ctx);
}

static void test_cb07(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk a = chunk(global, 0, 8);
    OspreyChunk b = chunk(global, 8, 8);
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x10, &b, 1, 1);
    OspreyBaseFact base;
    memset(&base, 0, sizeof(base));
    base.pc = 0x10;
    base.chunk = a;
    base.base = a.address;
    g_array_append_val(ctx->base_facts, base);
    CHECK(build_secondary(ctx), "CB07 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CB07) == 1,
          "CB07 matches complete BaseAddr identity");
    uint32_t access = access_variable_id(ctx, 0x10, &a);
    uint32_t start = start_variable_id(ctx, &a.address);
    uint32_t ids[2] = { access, start };
    expect_factor(ctx, OSPREY_RULE_CB07, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  ids, 2, "CB07 exact access-to-start factor");
    const FactorExpectation cb07_block[] = {
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.8,
          1, ids, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CB07, cb07_block,
                        G_N_ELEMENTS(cb07_block),
                        "CB07 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CB07, 1,
                               "CB07 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CB07, 1, 8, 0,
                                "CB07 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x10, &b, 1, 1);
    base.pc = 0x20;
    g_array_append_val(ctx->base_facts, base);
    CHECK(build_secondary(ctx), "CB07 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CB07) == 0,
          "CB07 rejects a PC mismatch");
    osprey_free(ctx);

    ctx = new_context();
    OspreyRegionId stack = region(OSPREY_REGION_STACK_FUNCTION, 9);
    OspreyChunk other_region = chunk(stack, 0, 8);
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x10, &b, 1, 1);
    base.pc = 0x10;
    base.chunk = other_region;
    base.base = other_region.address;
    g_array_append_val(ctx->base_facts, base);
    CHECK(build_secondary(ctx), "CB07 region mismatch");
    CHECK(rule_count(ctx, OSPREY_RULE_CB07) == 0,
          "CB07 rejects a BaseAddr region mismatch");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk unaccessed = chunk(global, 16, 8);
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x10, &b, 1, 1);
    base.pc = 0x10;
    base.chunk = unaccessed;
    base.base = unaccessed.address;
    g_array_append_val(ctx->base_facts, base);
    CHECK(build_secondary(ctx), "CB07 chunk mismatch");
    CHECK(rule_count(ctx, OSPREY_RULE_CB07) == 0,
          "CB07 rejects an unaccessed chunk mismatch");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x10, &b, 1, 1);
    base.pc = 0x10;
    base.chunk = a;
    base.base = address(stack, 0);
    g_array_append_val(ctx->base_facts, base);
    CHECK(osprey_stage3_base(ctx) == OSPREY_INVALID_GRAPH,
          "CB07 rejects a BaseAddr base-region mismatch");
    osprey_free(ctx);
}

static void test_cb08(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk a = chunk(global, 0, 8);
    OspreyChunk b = chunk(global, 8, 8);
    add_logical(ctx, 0x10, &a, 9, 1);
    add_logical(ctx, 0x10, &b, 1, 1);
    CHECK(build_secondary(ctx), "CB08 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CB08) == 1,
          "CB08 emits the most-frequent address");
    uint32_t access = access_variable_id(ctx, 0x10, &a);
    uint32_t start = start_variable_id(ctx, &a.address);
    uint32_t ids[2] = { access, start };
    expect_factor(ctx, OSPREY_RULE_CB08, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.25, 1,
                  ids, 2, "CB08 exact logical-support factor");
    const FactorExpectation cb08_block[] = {
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, false, 0.25,
          1, ids, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CB08, cb08_block,
                        G_N_ELEMENTS(cb08_block),
                        "CB08 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CB08, 1,
                               "CB08 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CB08, 1, 6, 0,
                                "CB08 exact proposal/kept/dropped totals");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk narrow = chunk(global, 0, 4);
    OspreyChunk wide = chunk(global, 0, 8);
    OspreyChunk other = chunk(global, 16, 8);
    add_logical(ctx, 0x10, &narrow, 9, 1);
    add_logical(ctx, 0x10, &wide, 1, 1);
    add_logical(ctx, 0x10, &other, 2, 1);
    CHECK(build_secondary(ctx), "CB08 same-address width frequencies");
    CHECK(rule_count(ctx, OSPREY_RULE_CB08) == 1,
          "CB08 uses only chunks carrying the R07 maximum count");
    uint32_t narrow_access = access_variable_id(ctx, 0x10, &narrow);
    uint32_t narrow_start = start_variable_id(ctx, &narrow.address);
    uint32_t narrow_ids[2] = { narrow_access, narrow_start };
    expect_factor(ctx, OSPREY_RULE_CB08, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.25, 1,
                  narrow_ids, 2, "CB08 exact winning-width factor");
    CHECK(!factor_exact(ctx, OSPREY_RULE_CB08, OSPREY_GRAPH_SECONDARY,
                        OSPREY_POTENTIAL_IMPLICATION, false, 0.25, 1,
                        (uint32_t[2]){
                            access_variable_id(ctx, 0x10, &wide),
                            start_variable_id(ctx, &wide.address)
                        }, 2),
          "CB08 excludes lower-frequency width at tied address");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 3, 1);
    add_logical(ctx, 0x10, &b, 3, 1);
    CHECK(build_secondary(ctx), "CB08 tied addresses");
    CHECK(rule_count(ctx, OSPREY_RULE_CB08) == 2,
          "CB08 retains every R07 maximum address");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk third = chunk(global, 16, 8);
    add_logical(ctx, 0x10, &third, 3, 1);
    add_logical(ctx, 0x10, &b, 3, 1);
    add_logical(ctx, 0x10, &a, 3, 1);
    CHECK(build_secondary(ctx), "CB08 three-way dynamic tie");
    CHECK(rule_count(ctx, OSPREY_RULE_CB08) == 3,
          "CB08 retains all three tied maxima");
    OspreyChunk tied_chunks[3] = { a, b, third };
    for (guint i = 0; i < G_N_ELEMENTS(tied_chunks); i++) {
        uint32_t tied_access = access_variable_id(ctx, 0x10,
                                                   &tied_chunks[i]);
        uint32_t tied_start = start_variable_id(ctx,
                                                 &tied_chunks[i].address);
        uint32_t tied_ids[2] = { tied_access, tied_start };
        expect_factor(ctx, OSPREY_RULE_CB08, OSPREY_GRAPH_SECONDARY,
                      OSPREY_POTENTIAL_IMPLICATION, false, 0.25, 1,
                      tied_ids, 2, "CB08 exact tied maximum factor");
    }
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    CHECK(build_secondary(ctx), "CB08 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CB08) == 0,
          "CB08 requires a multi-chunk group");
    osprey_free(ctx);
}

static void test_cb09(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk a = chunk(global, 0, 8);
    OspreyChunk b = chunk(global, 8, 8);
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x10, &b, 1, 1);
    OspreyBaseFact first;
    memset(&first, 0, sizeof(first));
    first.pc = 0x10;
    first.chunk = a;
    first.base = a.address;
    g_array_append_val(ctx->base_facts, first);
    first.chunk = b;
    first.base = b.address;
    g_array_append_val(ctx->base_facts, first);
    CHECK(build_secondary(ctx), "CB09 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CB09) == 1,
          "CB09 emits one ordered negative implication");
    uint32_t first_start = start_variable_id(ctx, &a.address);
    uint32_t second_start = start_variable_id(ctx, &b.address);
    uint32_t ids[2] = { first_start, second_start };
    expect_factor(ctx, OSPREY_RULE_CB09, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  ids, 2, "CB09 exact ordered exclusion");
    const FactorExpectation cb09_block[] = {
        { OSPREY_GRAPH_SECONDARY, OSPREY_POTENTIAL_IMPLICATION, true, 0.2,
          1, ids, 2 },
    };
    expect_factor_block(ctx, OSPREY_RULE_CB09, cb09_block,
                        G_N_ELEMENTS(cb09_block),
                        "CB09 complete canonical factor block");
    expect_candidate_proposals(ctx, OSPREY_RULE_CB09, 0,
                               "CB09 exact proposal count");
    expect_candidate_accounting(ctx, OSPREY_RULE_CB09, 0, 9, 0,
                                "CB09 exact proposal/kept/dropped totals");
    uint32_t reverse_ids[2] = { second_start, first_start };
    CHECK(!factor_exact(ctx, OSPREY_RULE_CB09, OSPREY_GRAPH_SECONDARY,
                        OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                        reverse_ids, 2),
          "CB09 does not invent reverse ordering");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical_value(ctx, 0x10, chunk(global, 0, 8), 1, 1);
    CHECK(build_secondary(ctx), "CB09 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CB09) == 0,
          "CB09 rejects equal starts");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &b, 1, 1);
    add_logical(ctx, 0x10, &a, 1, 1);
    CHECK(seed_array_start(ctx, &a.address).inserted,
          "CB09 reversed lower start");
    CHECK(seed_array_start(ctx, &b.address).inserted,
          "CB09 reversed higher start");
    CHECK(build_secondary(ctx), "CB09 reversed input order");
    CHECK(rule_count(ctx, OSPREY_RULE_CB09) == 1,
          "CB09 canonicalizes reversed input order");
    first_start = start_variable_id(ctx, &a.address);
    second_start = start_variable_id(ctx, &b.address);
    ids[0] = first_start;
    ids[1] = second_start;
    expect_factor(ctx, OSPREY_RULE_CB09, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  ids, 2, "CB09 reversed input keeps low-to-high factor");
    osprey_free(ctx);

    ctx = new_context();
    OspreyRegionId stack = region(OSPREY_REGION_STACK_FUNCTION, 11);
    OspreyChunk other_region = chunk(stack, 8, 8);
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical(ctx, 0x10, &other_region, 1, 1);
    CHECK(seed_array_start(ctx, &a.address).inserted,
          "CB09 region lower start");
    CHECK(seed_array_start(ctx, &other_region.address).inserted,
          "CB09 region higher start");
    CHECK(build_secondary(ctx), "CB09 region mismatch");
    CHECK(rule_count(ctx, OSPREY_RULE_CB09) == 0,
          "CB09 rejects a region mismatch");
    osprey_free(ctx);
}

static void test_cc01(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x101);
    add_allocation(ctx, heap.site_offset, 0);
    CHECK(build_secondary(ctx), "CC01 zero-size singleton");
    CHECK(rule_count(ctx, OSPREY_RULE_CC01) == 2 &&
          rule_count(ctx, OSPREY_RULE_CC02) == 0,
          "CC01 emits only its two singleton priors");
    uint32_t unfoldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_UNFOLDABLE_HEAP, heap, 0);
    uint32_t foldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_FOLDABLE_HEAP, heap, 0);
    expect_factor(ctx, OSPREY_RULE_CC01, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_PRIOR, false, 0.8, 0,
                  &unfoldable, 1, "CC01 zero-size unfoldable prior");
    expect_factor(ctx, OSPREY_RULE_CC01, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_PRIOR, false, 0.8, 0,
                  &foldable, 1, "CC01 zero-size foldable prior");
    expect_candidate_proposals(ctx, OSPREY_RULE_CC01, 2,
                               "CC01 singleton proposal count");
    osprey_free(ctx);

    ctx = new_context();
    heap = region(OSPREY_REGION_HEAP_SITE, 0x102);
    add_allocation(ctx, heap.site_offset, ((uint64_t)INT64_MAX));
    CHECK(build_secondary(ctx), "CC01 maximum singleton");
    CHECK(rule_count(ctx, OSPREY_RULE_CC01) == 2,
          "CC01 represents INT64_MAX singleton size");
    osprey_free(ctx);

    ctx = new_context();
    heap = region(OSPREY_REGION_HEAP_SITE, 0x103);
    add_allocation(ctx, heap.site_offset, 0);
    add_allocation(ctx, heap.site_offset, 16);
    CHECK(build_secondary(ctx), "CC01 two-size near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CC01) == 0 &&
          rule_count(ctx, OSPREY_RULE_CC02) == 1,
          "CC01 excludes a varied allocation site");
    osprey_free(ctx);
}

static void test_cc02(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x201);
    add_allocation(ctx, heap.site_offset, 48);
    add_allocation(ctx, heap.site_offset, 0);
    add_allocation(ctx, heap.site_offset, 16);
    add_allocation(ctx, heap.site_offset, 16);
    CHECK(build_secondary(ctx), "CC02 positive GCD");
    CHECK(rule_count(ctx, OSPREY_RULE_CC02) == 1 &&
          rule_count(ctx, OSPREY_RULE_CC01) == 0,
          "CC02 uses the positive GCD for varied sizes");
    uint32_t unit = heap_fold_variable_id(
        ctx, OSPREY_PRED_FOLDABLE_HEAP, heap, 16);
    expect_factor(ctx, OSPREY_RULE_CC02, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_PRIOR, false, 0.8, 0,
                  &unit, 1, "CC02 exact unit prior");
    osprey_free(ctx);

    ctx = new_context();
    heap = region(OSPREY_REGION_HEAP_SITE, 0x202);
    add_allocation(ctx, heap.site_offset, 24);
    CHECK(build_secondary(ctx), "CC02 constant-only near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CC02) == 0,
          "CC02 excludes singleton allocation sites");
    osprey_free(ctx);

    ctx = new_context();
    heap = region(OSPREY_REGION_HEAP_SITE, 0x203);
    add_allocation(ctx, heap.site_offset, 0);
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "CC02 malformed-unit relation setup");
    OspreyAllocRelation malformed;
    memset(&malformed, 0, sizeof(malformed));
    malformed.site_pc = heap.site_offset;
    malformed.size = 0;
    g_array_append_val(ctx->relations->r09_alloc_unit, malformed);
    CHECK(osprey_stage3_secondary(ctx) == OSPREY_INVALID_GRAPH,
          "CC02 rejects an impossible zero unit");
    osprey_free(ctx);
}

static void test_cc03(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x301);
    OspreyChunk value = chunk(heap, 8, 8);
    add_allocation(ctx, heap.site_offset, 32);
    add_logical(ctx, 0x10, &value, 1, 1);
    CHECK(build_secondary(ctx), "CC03 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CC03) == 1,
          "CC03 emits the primitive-to-heap-end implication");
    uint32_t primitive = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                           &value);
    uint32_t unfoldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_UNFOLDABLE_HEAP, heap, 16);
    uint32_t ids[2] = { primitive, unfoldable };
    expect_factor(ctx, OSPREY_RULE_CC03, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  ids, 2, "CC03 exact checked heap end");
    osprey_free(ctx);

    ctx = new_context();
    heap = region(OSPREY_REGION_HEAP_SITE, 0x302);
    value = chunk(heap, 0, 8);
    add_allocation(ctx, heap.site_offset, 8);
    add_logical(ctx, 0x10, &value, 1, 1);
    CHECK(build_secondary(ctx), "CC03 zero-offset heap chunk");
    CHECK(rule_count(ctx, OSPREY_RULE_CC03) == 1,
          "CC03 accepts a heap chunk at offset zero");
    osprey_free(ctx);

    ctx = new_context();
    heap = region(OSPREY_REGION_HEAP_SITE, 0x305);
    value = chunk(heap, 24, 8);
    add_allocation(ctx, heap.site_offset, 32);
    add_logical(ctx, 0x10, &value, 1, 1);
    CHECK(build_secondary(ctx), "CC03 exact extent end");
    CHECK(rule_count(ctx, OSPREY_RULE_CC03) >= 1,
          "CC03 permits an exact allocation extent end");
    osprey_free(ctx);

    ctx = new_context();
    heap = region(OSPREY_REGION_HEAP_SITE, 0x303);
    value = chunk(heap, -1, 1);
    add_allocation(ctx, heap.site_offset, 32);
    add_logical(ctx, 0x10, &value, 1, 1);
    CHECK(osprey_stage3_build(ctx) == OSPREY_INVALID_GRAPH,
          "CC03 rejects a negative heap offset");
    osprey_free(ctx);

    ctx = new_context();
    heap = region(OSPREY_REGION_HEAP_SITE, 0x304);
    value = chunk(heap, INT64_MAX, 1);
    add_allocation(ctx, heap.site_offset, ((uint64_t)INT64_MAX));
    add_logical(ctx, 0x10, &value, 1, 1);
    CHECK(osprey_stage3_build(ctx) == OSPREY_GRAPH_ARITHMETIC,
          "CC03 rejects heap-end overflow");
    osprey_free(ctx);
}

static void test_cc04(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x401);
    CHECK(seed_heap_unfoldable(ctx, heap, 24).inserted,
          "CC04 largest prefix seed");
    CHECK(seed_heap_unfoldable(ctx, heap, 8).inserted,
          "CC04 smallest prefix seed");
    CHECK(seed_heap_unfoldable(ctx, heap, 16).inserted,
          "CC04 middle prefix seed");
    CHECK(build_secondary(ctx), "CC04 permuted prefixes");
    CHECK(rule_count(ctx, OSPREY_RULE_CC04) == 6,
          "CC04 emits both directions for all prefix pairs");
    osprey_free(ctx);

    ctx = new_context();
    heap = region(OSPREY_REGION_HEAP_SITE, 0x402);
    CHECK(seed_heap_unfoldable(ctx, heap, 8).inserted,
          "CC04 equal-prefix seed");
    CHECK(build_secondary(ctx), "CC04 equal-prefix near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CC04) == 0 &&
          rule_count(ctx, OSPREY_RULE_CC05) == 0,
          "CC04/CC05 omit equal prefix self-factors");
    osprey_free(ctx);
}

static void test_cc05(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x501);
    seed_heap_unfoldable(ctx, heap, 24);
    seed_heap_unfoldable(ctx, heap, 8);
    seed_heap_unfoldable(ctx, heap, 16);
    CHECK(build_secondary(ctx), "CC05 permuted prefixes");
    CHECK(rule_count(ctx, OSPREY_RULE_CC05) == 3,
          "CC05 supports every smaller prefix exactly once");
    osprey_free(ctx);

    ctx = new_context();
    heap = region(OSPREY_REGION_HEAP_SITE, 0x502);
    seed_heap_unfoldable(ctx, heap, 8);
    seed_heap_unfoldable(ctx, region(OSPREY_REGION_HEAP_SITE, 0x503), 16);
    CHECK(build_secondary(ctx), "CC05 site identity near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CC05) == 0,
          "CC05 does not merge allocation sites");
    osprey_free(ctx);
}

static void test_cc06(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x601);
    add_allocation(ctx, heap.site_offset, 32);
    CHECK(seed_array(ctx, heap, 0, 32, 8).inserted,
          "CC06 heap array seed");
    CHECK(build_secondary(ctx), "CC06 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CC06) == 1,
          "CC06 emits the array-to-stride implication");
    uint32_t array = array_variable_id(ctx, heap, 0, 32, 8);
    uint32_t foldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_FOLDABLE_HEAP, heap, 8);
    uint32_t ids[2] = { array, foldable };
    expect_factor(ctx, OSPREY_RULE_CC06, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  ids, 2, "CC06 exact stride factor");
    osprey_free(ctx);

    ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk extent = chunk(global, 0, 32);
    add_extent(ctx, &extent);
    seed_array(ctx, global, 0, 32, 8);
    CHECK(build_secondary(ctx), "CC06 non-heap near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CC06) == 0,
          "CC06 requires the matching heap-site region");
    osprey_free(ctx);

    ctx = new_context();
    heap = region(OSPREY_REGION_HEAP_SITE, 0x602);
    add_allocation(ctx, heap.site_offset, 16);
    CHECK(seed_array(ctx, heap, 0, 32, 8).inserted,
          "CC06 oversized heap array seed");
    CHECK(build_base(ctx), "CC06 oversized-array base setup");
    CHECK(osprey_stage3_secondary(ctx) == OSPREY_INVALID_GRAPH,
          "CC06 rejects an array beyond the allocation extent");
    osprey_free(ctx);
}

static OspreyContext *cc07_context(uint64_t allocation_size,
                                   uint64_t sh, uint64_t st,
                                   int64_t value_offset, uint64_t width,
                                   int64_t folded_offset)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x701);
    OspreyChunk value = chunk(heap, value_offset, width);
    OspreyChunk folded = chunk(heap, folded_offset, width);
    add_allocation(ctx, heap.site_offset, allocation_size);
    CHECK(osprey_candidate_select(ctx, NULL, 0) == OSPREY_OK,
          "CC07 allocation extent catalog");
    seed_primitive(ctx, value);
    seed_heap_unfoldable(ctx, heap, sh);
    seed_heap_foldable(ctx, heap, st);
    seed_primitive(ctx, folded);
    return ctx;
}

static void test_cc07(void)
{
    OspreyContext *ctx = cc07_context(16, 8, 4, 12, 4, 8);
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "CC07 relation fixture");
    OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x701);
    uint32_t primitive = chunk_variable_id_value(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, heap, 12, 4);
    uint32_t folded = chunk_variable_id_value(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, heap, 8, 4);
    uint32_t unfoldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_UNFOLDABLE_HEAP,
        region(OSPREY_REGION_HEAP_SITE, 0x701), 8);
    uint32_t foldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_FOLDABLE_HEAP,
        region(OSPREY_REGION_HEAP_SITE, 0x701), 4);
    CHECK(osprey_compile_cc07(ctx, primitive, unfoldable, foldable, folded) ==
              OSPREY_OK,
          "CC07 positive compiler");
    CHECK(rule_count(ctx, OSPREY_RULE_CC07) == 2,
          "CC07 emits positive and negative factors");
    uint32_t positive[4] = { primitive, unfoldable, foldable, folded };
    uint32_t negative[3] = { unfoldable, foldable, primitive };
    expect_factor(ctx, OSPREY_RULE_CC07, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 3,
                  positive, 4, "CC07 exact folded implication");
    expect_factor(ctx, OSPREY_RULE_CC07, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 2,
                  negative, 3, "CC07 exact source exclusion");
    osprey_free(ctx);

    ctx = cc07_context(16, 8, 0, 12, 4, 8);
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "CC07 zero-stride relation fixture");
    primitive = chunk_variable_id_value(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, heap, 12, 4);
    unfoldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_UNFOLDABLE_HEAP,
        region(OSPREY_REGION_HEAP_SITE, 0x701), 8);
    foldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_FOLDABLE_HEAP,
        region(OSPREY_REGION_HEAP_SITE, 0x701), 0);
    folded = chunk_variable_id_value(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, heap, 8, 4);
    CHECK(osprey_compile_cc07(ctx, primitive, unfoldable, foldable, folded) ==
              OSPREY_INVALID_GRAPH,
          "CC07 rejects zero stride before modulo");
    osprey_free(ctx);

    ctx = cc07_context(16, 8, 4, 11, 4, 11);
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "CC07 threshold near-miss relation fixture");
    primitive = chunk_variable_id_value(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, heap, 11, 4);
    unfoldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_UNFOLDABLE_HEAP,
        region(OSPREY_REGION_HEAP_SITE, 0x701), 8);
    foldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_FOLDABLE_HEAP,
        region(OSPREY_REGION_HEAP_SITE, 0x701), 4);
    folded = chunk_variable_id_value(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, heap, 11, 4);
    CHECK(osprey_compile_cc07(ctx, primitive, unfoldable, foldable, folded) ==
              OSPREY_INVALID_GRAPH,
          "CC07 rejects offset below sh plus st");
    osprey_free(ctx);

    ctx = cc07_context(18, 8, 4, 14, 4, 10);
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "CC07 modulo relation fixture");
    primitive = chunk_variable_id_value(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, heap, 14, 4);
    unfoldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_UNFOLDABLE_HEAP,
        region(OSPREY_REGION_HEAP_SITE, 0x701), 8);
    foldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_FOLDABLE_HEAP,
        region(OSPREY_REGION_HEAP_SITE, 0x701), 4);
    folded = chunk_variable_id_value(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, heap, 10, 4);
    CHECK(osprey_compile_cc07(ctx, primitive, unfoldable, foldable, folded) ==
              OSPREY_OK,
          "CC07 applies the checked modulo offset");
    osprey_free(ctx);

    ctx = cc07_context(15, 8, 4, 12, 4, 8);
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "CC07 short-allocation relation fixture");
    primitive = chunk_variable_id_value(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, heap, 12, 4);
    unfoldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_UNFOLDABLE_HEAP, heap, 8);
    foldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_FOLDABLE_HEAP, heap, 4);
    folded = chunk_variable_id_value(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, heap, 8, 4);
    CHECK(osprey_compile_cc07(ctx, primitive, unfoldable, foldable, folded) ==
              OSPREY_INVALID_GRAPH,
          "CC07 rejects a source beyond the allocation extent");
    osprey_free(ctx);

    ctx = cc07_context(INT64_MAX, INT64_MAX, 1, INT64_MAX, 1, 0);
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "CC07 allocation-overflow relation fixture");
    primitive = chunk_variable_id_value(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, heap, INT64_MAX, 1);
    unfoldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_UNFOLDABLE_HEAP,
        region(OSPREY_REGION_HEAP_SITE, 0x701), INT64_MAX);
    foldable = heap_fold_variable_id(
        ctx, OSPREY_PRED_FOLDABLE_HEAP,
        region(OSPREY_REGION_HEAP_SITE, 0x701), 1);
    folded = chunk_variable_id_value(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, heap, 0, 1);
    CHECK(osprey_compile_cc07(ctx, primitive, unfoldable, foldable, folded) ==
              OSPREY_GRAPH_ARITHMETIC,
          "CC07 rejects allocation extent overflow");
    osprey_free(ctx);
}

static void test_cd01(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    add_copy_fact(ctx, chunk(global, 0, 8), chunk(global, 100, 8));
    add_copy_fact(ctx, chunk(global, 16, 8), chunk(global, 116, 8));
    CHECK(build_secondary(ctx), "CD01 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CD01) == 1,
          "CD01 emits one data-flow prior");
    uint32_t homo = homo_variable_id(ctx, address(global, 0),
                                     address(global, 100), 16);
    expect_factor(ctx, OSPREY_RULE_CD01, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_PRIOR, false, 0.8, 0,
                  &homo, 1, "CD01 exact matched delta");
    osprey_free(ctx);

    ctx = new_context();
    add_copy_fact(ctx, chunk(global, 0, 8), chunk(global, 100, 8));
    add_copy_fact(ctx, chunk(global, 16, 8), chunk(global, 117, 8));
    CHECK(build_secondary(ctx), "CD01 destination-delta near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD01) == 0,
          "CD01 rejects mismatched destination delta");
    osprey_free(ctx);
}

static void populate_cd02(OspreyContext *ctx, bool reverse)
{
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk first_target = chunk(global, 0, 8);
    OspreyChunk first_value = chunk(global, 8, 8);
    OspreyChunk second_target = chunk(global, 16, 8);
    OspreyChunk second_value = chunk(global, 24, 8);
    OspreyChunk pointer = chunk(global, 32, 8);
    if (!reverse) {
        add_logical(ctx, 0x10, &first_target, 1, 1);
        add_logical(ctx, 0x10, &first_value, 1, 1);
        add_logical(ctx, 0x10, &second_target, 1, 1);
        add_logical(ctx, 0x10, &second_value, 1, 1);
        add_base_fact(ctx, first_value, first_target.address);
        add_base_fact(ctx, second_value, second_target.address);
        add_points_fact(ctx, pointer, first_target.address);
        add_points_fact(ctx, pointer, second_target.address);
    } else {
        add_logical(ctx, 0x10, &second_value, 1, 1);
        add_logical(ctx, 0x10, &second_target, 1, 1);
        add_logical(ctx, 0x10, &first_value, 1, 1);
        add_logical(ctx, 0x10, &first_target, 1, 1);
        add_base_fact(ctx, second_value, second_target.address);
        add_base_fact(ctx, first_value, first_target.address);
        add_points_fact(ctx, pointer, second_target.address);
        add_points_fact(ctx, pointer, first_target.address);
    }
}

static void test_cd02(void)
{
    OspreyContext *ctx = new_context();
    populate_cd02(ctx, false);
    CHECK(build_secondary(ctx), "CD02 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CD02) == 1,
          "CD02 emits one points-to prior");
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    uint32_t homo = homo_variable_id(ctx, address(global, 0),
                                     address(global, 16), 8);
    expect_factor(ctx, OSPREY_RULE_CD02, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_PRIOR, false, 0.8, 0,
                  &homo, 1, "CD02 exact base/access join");
    osprey_free(ctx);

    ctx = new_context();
    populate_cd02(ctx, true);
    CHECK(build_secondary(ctx), "CD02 permuted input");
    CHECK(rule_count(ctx, OSPREY_RULE_CD02) == 1,
          "CD02 keeps canonical result under permutation");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk first_target = chunk(global, 0, 8);
    OspreyChunk first_value = chunk(global, 8, 8);
    OspreyChunk second_target = chunk(global, 16, 8);
    OspreyChunk second_value = chunk(global, 24, 8);
    OspreyChunk pointer = chunk(global, 32, 8);
    add_logical(ctx, 0x10, &first_target, 1, 1);
    add_logical(ctx, 0x10, &first_value, 1, 1);
    add_logical(ctx, 0x10, &second_target, 1, 1);
    add_logical(ctx, 0x10, &second_value, 1, 1);
    add_base_fact(ctx, first_value, first_target.address);
    add_base_fact(ctx, second_value, second_target.address);
    add_points_fact(ctx, pointer, address(global, 17));
    add_points_fact(ctx, pointer, first_target.address);
    CHECK(build_secondary(ctx), "CD02 target-address near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD02) == 0,
          "CD02 requires exact pointer targets");
    osprey_free(ctx);
}

static void populate_cd03(OspreyContext *ctx, bool reverse,
                          int64_t second_delta)
{
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk first = chunk(global, 0, 8);
    OspreyChunk second = chunk(global, 8, 8);
    OspreyChunk third = chunk(global, 16, 8);
    OspreyChunk fourth = chunk(global, 24 + second_delta - 16, 8);
    if (!reverse) {
        add_logical(ctx, 0x10, &first, 1, 1);
        add_logical(ctx, 0x10, &second, 1, 1);
        add_logical(ctx, 0x20, &third, 1, 1);
        add_logical(ctx, 0x20, &fourth, 1, 1);
    } else {
        add_logical(ctx, 0x20, &fourth, 1, 1);
        add_logical(ctx, 0x20, &third, 1, 1);
        add_logical(ctx, 0x10, &second, 1, 1);
        add_logical(ctx, 0x10, &first, 1, 1);
    }
}

static void test_cd03(void)
{
    OspreyContext *ctx = new_context();
    populate_cd03(ctx, false, 16);
    CHECK(build_secondary(ctx), "CD03 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CD03) == 1,
          "CD03 emits one unified-access prior");
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    uint32_t homo = homo_variable_id(ctx, address(global, 0),
                                     address(global, 8), 16);
    expect_factor(ctx, OSPREY_RULE_CD03, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_PRIOR, false, 0.8, 0,
                  &homo, 1, "CD03 exact corresponding access delta");
    osprey_free(ctx);

    ctx = new_context();
    populate_cd03(ctx, true, 16);
    CHECK(build_secondary(ctx), "CD03 permuted input");
    CHECK(rule_count(ctx, OSPREY_RULE_CD03) == 1,
          "CD03 keeps canonical result under permutation");
    osprey_free(ctx);

    ctx = new_context();
    populate_cd03(ctx, false, 17);
    CHECK(build_secondary(ctx), "CD03 skew near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD03) == 0,
          "CD03 rejects unequal corresponding deltas");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk first = chunk(global, 0, 8);
    OspreyChunk second = chunk(global, 16, 8);
    add_logical(ctx, 0x10, &first, 1, 1);
    add_logical(ctx, 0x20, &second, 1, 1);
    CHECK(build_base(ctx), "CD03 malformed-hint base setup");
    OspreyHint malformed;
    memset(&malformed, 0, sizeof(malformed));
    malformed.a1 = first.address;
    malformed.a2 = second.address;
    malformed.size = 8;
    malformed.kind = UINT8_MAX;
    malformed.instances = 1;
    g_array_append_val(ctx->graph->hints, malformed);
    CHECK(osprey_stage3_secondary(ctx) == OSPREY_INVALID_GRAPH,
          "CD hint compiler rejects an unknown relation kind");
    osprey_free(ctx);
}

static void test_cd04(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk extent = chunk(global, 0, 48);
    OspreyChunk starts[4] = {
        chunk(global, 0, 1), chunk(global, 4, 1),
        chunk(global, 32, 1), chunk(global, 36, 1)
    };
    add_extent(ctx, &extent);
    for (guint i = 0; i < G_N_ELEMENTS(starts); i++) {
        add_logical(ctx, 0x10 + i, &starts[i], 1, 1);
    }
    CHECK(seed_homo(ctx, address(global, 0), address(global, 32), 16).inserted,
          "CD04 first candidate");
    CHECK(seed_homo(ctx, address(global, 4), address(global, 36), 8).inserted,
          "CD04 second candidate");
    CHECK(build_secondary(ctx), "CD04 positive closure");
    CHECK(rule_count(ctx, OSPREY_RULE_CD04) >= 3,
          "CD04 emits directional factors and a checked union");
    CHECK(homo_variable_id(ctx, address(global, 0), address(global, 32), 12) !=
              UINT32_MAX,
          "CD04 interns the union candidate");
    osprey_free(ctx);

    ctx = new_context();
    add_extent(ctx, &extent);
    for (guint i = 0; i < G_N_ELEMENTS(starts); i++) {
        add_logical(ctx, 0x10 + i, &starts[i], 1, 1);
    }
    seed_homo(ctx, address(global, 0), address(global, 32), 16);
    seed_homo(ctx, address(global, 4), address(global, 37), 8);
    CHECK(build_secondary(ctx), "CD04 partner-delta near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD04) == 0,
          "CD04 rejects mismatched partner deltas");
    osprey_free(ctx);

    ctx = new_context();
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &starts[0], 1, 1);
    add_logical(ctx, 0x20, &starts[2], 1, 1);
    seed_homo(ctx, address(global, 0), address(global, 32), 16);
    seed_homo(ctx, address(global, 0), address(global, 32), 8);
    CHECK(build_secondary(ctx), "CD04 zero-delta near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD04) == 0,
          "CD04 requires a positive endpoint delta");
    osprey_free(ctx);

    ctx = new_context();
    add_extent(ctx, &extent);
    for (guint i = 0; i < G_N_ELEMENTS(starts); i++) {
        add_logical(ctx, 0x10 + i, &starts[i], 1, 1);
    }
    seed_homo(ctx, address(global, 0), address(global, 32), 4);
    seed_homo(ctx, address(global, 4), address(global, 36), 8);
    CHECK(build_secondary(ctx), "CD04 touching-segment near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD04) == 0,
          "CD04 excludes delta equal to the first segment size");
    osprey_free(ctx);

    ctx = new_context();
    OspreyRegionId stack = region(OSPREY_REGION_STACK_FUNCTION, 0x404);
    OspreyChunk overflow_starts[4] = {
        chunk(global, 0, 1), chunk(global, 4, 1),
        chunk(stack, INT64_MAX - 10, 1), chunk(stack, INT64_MAX - 6, 1),
    };
    for (guint i = 0; i < G_N_ELEMENTS(overflow_starts); i++) {
        add_logical(ctx, 0x30 + i, &overflow_starts[i], 1, 1);
    }
    seed_homo(ctx, overflow_starts[0].address,
              overflow_starts[2].address, 8);
    seed_homo(ctx, overflow_starts[1].address,
              overflow_starts[3].address, 8);
    CHECK(build_base(ctx), "CD04 overflow base setup");
    CHECK(osprey_stage3_secondary(ctx) == OSPREY_GRAPH_ARITHMETIC,
          "CD04 rejects an overflowing union endpoint");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk chain_extent = chunk(global, 0, 48);
    OspreyChunk chain_starts[6] = {
        chunk(global, 0, 1), chunk(global, 4, 1), chunk(global, 8, 1),
        chunk(global, 32, 1), chunk(global, 36, 1), chunk(global, 40, 1),
    };
    add_extent(ctx, &chain_extent);
    for (guint i = 0; i < G_N_ELEMENTS(chain_starts); i++) {
        add_logical(ctx, 0x40 + i, &chain_starts[i], 1, 1);
    }
    seed_homo(ctx, address(global, 0), address(global, 32), 8);
    seed_homo(ctx, address(global, 4), address(global, 36), 8);
    seed_homo(ctx, address(global, 8), address(global, 40), 8);
    CHECK(build_secondary(ctx), "CD04 multi-round union closure");
    CHECK(homo_variable_id(ctx, address(global, 0),
                           address(global, 32), 16) != UINT32_MAX,
          "CD04 reaches a union requiring a derived intermediate");
    osprey_free(ctx);
}

static void test_cd05(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk extent = chunk(global, 0, 32);
    OspreyChunk first = chunk(global, 4, 4);
    OspreyChunk second = chunk(global, 20, 8);
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &first, 1, 1);
    add_logical(ctx, 0x20, &second, 1, 1);
    CHECK(seed_homo(ctx, address(global, 0), address(global, 16), 16).inserted,
          "CD05 segment seed");
    CHECK(build_secondary(ctx), "CD05 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CD05) == 3,
          "CD05 emits all three negative directions");
    uint32_t first_id = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                          &first);
    uint32_t second_id = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                           &second);
    uint32_t homo = homo_variable_id(ctx, address(global, 0),
                                     address(global, 16), 16);
    uint32_t pair[3] = { first_id, second_id, homo };
    expect_factor(ctx, OSPREY_RULE_CD05, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 2,
                  pair, 3, "CD05 conjunction-to-segment factor");
    uint32_t reverse_first[2] = { homo, first_id };
    uint32_t reverse_second[2] = { homo, second_id };
    expect_factor(ctx, OSPREY_RULE_CD05, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  reverse_first, 2, "CD05 segment-to-first factor");
    expect_factor(ctx, OSPREY_RULE_CD05, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 1,
                  reverse_second, 2, "CD05 segment-to-second factor");
    osprey_free(ctx);

    ctx = new_context();
    extent = chunk(global, 0, 32);
    first = chunk(global, 4, 4);
    second = chunk(global, 20, 4);
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &first, 1, 1);
    add_logical(ctx, 0x20, &second, 1, 1);
    seed_homo(ctx, address(global, 0), address(global, 16), 16);
    CHECK(build_secondary(ctx), "CD05 equal-width near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD05) == 0,
          "CD05 rejects matching widths");
    osprey_free(ctx);

    ctx = new_context();
    extent = chunk(global, 0, 32);
    first = chunk(global, 4, 4);
    second = chunk(global, 24, 8);
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &first, 1, 1);
    add_logical(ctx, 0x20, &second, 1, 1);
    seed_homo(ctx, address(global, 0), address(global, 16), 16);
    CHECK(build_secondary(ctx), "CD05 offset near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD05) == 0,
          "CD05 rejects mismatched corresponding offsets");
    osprey_free(ctx);

    ctx = new_context();
    extent = chunk(global, 0, 32);
    first = chunk(global, 0, 4);
    second = chunk(global, 16, 8);
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &first, 1, 1);
    add_logical(ctx, 0x20, &second, 1, 1);
    seed_homo(ctx, address(global, 0), address(global, 16), 16);
    CHECK(build_secondary(ctx), "CD05 segment-start near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD05) == 0,
          "CD05 enforces the positive-offset precondition");
    osprey_free(ctx);

    ctx = new_context();
    extent = chunk(global, 0, 32);
    first = chunk(global, 12, 4);
    second = chunk(global, 28, 2);
    add_extent(ctx, &extent);
    CHECK(seed_primitive(ctx, second).inserted,
          "CD05 reverse-ID right primitive seed");
    CHECK(seed_primitive(ctx, first).inserted,
          "CD05 reverse-ID left primitive seed");
    CHECK(seed_homo(ctx, address(global, 0), address(global, 16), 16).inserted,
          "CD05 boundary segment seed");
    CHECK(build_secondary(ctx), "CD05 exact-end semantic-order case");
    CHECK(rule_count(ctx, OSPREY_RULE_CD05) == 3,
          "CD05 permits a fully contained end-boundary field");
    first_id = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &first);
    second_id = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &second);
    homo = homo_variable_id(ctx, address(global, 0),
                            address(global, 16), 16);
    uint32_t ordered_pair[3] = { first_id, second_id, homo };
    CHECK(first_id > second_id,
          "CD05 fixture reverses allocation IDs relative to endpoint roles");
    expect_factor(ctx, OSPREY_RULE_CD05, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, true, 0.2, 2,
                  ordered_pair, 3, "CD05 preserves endpoint semantic order");
    osprey_free(ctx);
}

static void populate_cd06(OspreyContext *ctx, bool reverse,
                          bool target_access, bool cross_region)
{
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyRegionId stack = region(OSPREY_REGION_STACK_FUNCTION, 3);
    OspreyChunk source = chunk(global, 8, 4);
    OspreyChunk target = chunk(cross_region ? stack : global, 0, 4);
    if (!reverse) {
        add_logical(ctx, 0x10, &source, 1, 1);
        if (target_access) add_logical(ctx, 0x20, &target, 1, 1);
        add_base_fact(ctx, source, target.address);
    } else {
        add_base_fact(ctx, source, target.address);
        if (target_access) add_logical(ctx, 0x20, &target, 1, 1);
        add_logical(ctx, 0x10, &source, 1, 1);
    }
}

static void test_cd06(void)
{
    OspreyContext *ctx = new_context();
    populate_cd06(ctx, false, true, false);
    CHECK(build_secondary(ctx), "CD06 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CD06) == 1,
          "CD06 emits a source-target FieldOf implication");
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk source = chunk(global, 8, 4);
    OspreyChunk target = chunk(global, 0, 4);
    uint32_t source_id = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                           &source);
    uint32_t target_var_id = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                               &target);
    uint32_t field_id = field_variable_id(ctx, &source, &target.address);
    uint32_t ids[3] = { source_id, target_var_id, field_id };
    expect_factor(ctx, OSPREY_RULE_CD06, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 2,
                  ids, 3, "CD06 exact source and target roles");
    CHECK(field_id != UINT32_MAX, "CD06 interns the FieldOf head");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk wide_source = chunk(global, 8, 8);
    OspreyChunk narrow_target = chunk(global, 0, 4);
    OspreyChunk wide_target = chunk(global, 0, 8);
    OspreyChunk cd06_extent = chunk(global, 0, 16);
    add_extent(ctx, &cd06_extent);
    add_logical(ctx, 0x10, &wide_source, 1, 1);
    add_logical(ctx, 0x20, &narrow_target, 1, 1);
    add_logical(ctx, 0x30, &wide_target, 1, 1);
    add_base_fact(ctx, wide_source, narrow_target.address);
    CHECK(build_secondary(ctx), "CD06 multiple target widths");
    CHECK(rule_count(ctx, OSPREY_RULE_CD06) == 2,
          "CD06 retains each accessed target width witness");
    uint32_t multi_source_id = chunk_variable_id(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, &wide_source);
    uint32_t narrow_id = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                           &narrow_target);
    uint32_t wide_id = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                         &wide_target);
    uint32_t multi_field = field_variable_id(ctx, &wide_source,
                                              &narrow_target.address);
    uint32_t narrow_roles[3] = {
        multi_source_id, narrow_id, multi_field,
    };
    uint32_t wide_roles[3] = {
        multi_source_id, wide_id, multi_field,
    };
    expect_factor(ctx, OSPREY_RULE_CD06, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 2,
                  narrow_roles, 3, "CD06 narrow target role");
    expect_factor(ctx, OSPREY_RULE_CD06, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 2,
                  wide_roles, 3, "CD06 wide target role");
    osprey_free(ctx);

    ctx = new_context();
    populate_cd06(ctx, true, true, false);
    CHECK(build_secondary(ctx), "CD06 permuted input");
    CHECK(rule_count(ctx, OSPREY_RULE_CD06) == 1,
          "CD06 remains deterministic under permutation");
    osprey_free(ctx);

    ctx = new_context();
    populate_cd06(ctx, false, false, false);
    CHECK(build_secondary(ctx), "CD06 target-access near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD06) == 0,
          "CD06 requires target access");
    osprey_free(ctx);

    ctx = new_context();
    populate_cd06(ctx, false, true, true);
    CHECK(build_secondary(ctx), "CD06 cross-region near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD06) == 0,
          "CD06 excludes cross-region FieldOf");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk zero_field = chunk(global, 0, 4);
    add_logical(ctx, 0x10, &zero_field, 1, 1);
    add_base_fact(ctx, zero_field, zero_field.address);
    CHECK(build_secondary(ctx), "CD06 zero-offset self-base case");
    CHECK(rule_count(ctx, OSPREY_RULE_CD06) == 1,
          "CD06 retains a field whose base chunk is itself");
    uint32_t zero_primitive = chunk_variable_id(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, &zero_field);
    uint32_t zero_field_id = field_variable_id(
        ctx, &zero_field, &zero_field.address);
    uint32_t zero_roles[2] = { zero_primitive, zero_field_id };
    expect_factor(ctx, OSPREY_RULE_CD06, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  zero_roles, 2, "CD06 simplifies duplicate antecedents");
    osprey_free(ctx);
}

static void test_cd07(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x701);
    OspreyChunk value = chunk(heap, 4, 4);
    add_allocation(ctx, heap.site_offset, 16);
    add_logical(ctx, 0x10, &value, 1, 1);
    CHECK(build_secondary(ctx), "CD07 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CD07) == 1,
          "CD07 emits the heap-base FieldOf implication");
    OspreyAddress heap_base = address(heap, 0);
    uint32_t primitive = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                           &value);
    uint32_t field = field_variable_id(ctx, &value, &heap_base);
    uint32_t ids[2] = { primitive, field };
    expect_factor(ctx, OSPREY_RULE_CD07, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  ids, 2, "CD07 exact heap base factor");
    osprey_free(ctx);

    ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    value = chunk(global, 4, 4);
    OspreyChunk extent = chunk(global, 0, 16);
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &value, 1, 1);
    CHECK(build_secondary(ctx), "CD07 global near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD07) == 0,
          "CD07 excludes global regions");
    osprey_free(ctx);

    ctx = new_context();
    OspreyRegionId stack = region(OSPREY_REGION_STACK_FUNCTION, 0x702);
    value = chunk(stack, -8, 4);
    add_logical(ctx, 0x10, &value, 1, 1);
    CHECK(build_secondary(ctx), "CD07 stack near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD07) == 0,
          "CD07 excludes stack regions");
    osprey_free(ctx);
}

static void test_cd08(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk extent = chunk(global, 0, 64);
    OspreyChunk source = chunk(global, 0, 4);
    OspreyChunk target = chunk(global, 16, 4);
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &source, 1, 1);
    add_logical(ctx, 0x20, &target, 1, 1);
    seed_field(ctx, source, source.address);
    seed_homo(ctx, address(global, 0), address(global, 16), 16);
    CHECK(build_secondary(ctx), "CD08 offset-zero translation");
    CHECK(rule_count(ctx, OSPREY_RULE_CD08) == 2,
          "CD08 translates a complete field in both directions");
    uint32_t source_field = field_variable_id(ctx, &source, &source.address);
    uint32_t target_field = field_variable_id(ctx, &target, &target.address);
    uint32_t homo = homo_variable_id(ctx, address(global, 0),
                                     address(global, 16), 16);
    uint32_t ids[3] = { source_field, homo, target_field };
    expect_factor(ctx, OSPREY_RULE_CD08, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 2,
                  ids, 3, "CD08 exact translated-field factor");
    osprey_free(ctx);

    ctx = new_context();
    extent = chunk(global, 0, 64);
    source = chunk(global, 16, 4);
    target = chunk(global, 0, 4);
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &source, 1, 1);
    add_logical(ctx, 0x20, &target, 1, 1);
    seed_field(ctx, source, source.address);
    seed_homo(ctx, address(global, 0), address(global, 16), 16);
    CHECK(build_secondary(ctx), "CD08 reverse translation");
    CHECK(rule_count(ctx, OSPREY_RULE_CD08) == 2,
          "CD08 repeats in the reverse endpoint direction");
    osprey_free(ctx);

    ctx = new_context();
    extent = chunk(global, 0, 64);
    source = chunk(global, 15, 4);
    target = chunk(global, 31, 4);
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &source, 1, 1);
    add_logical(ctx, 0x20, &target, 1, 1);
    seed_field(ctx, source, address(global, 0));
    seed_homo(ctx, address(global, 0), address(global, 16), 16);
    CHECK(build_secondary(ctx), "CD08 span near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD08) == 0,
          "CD08 rejects fields extending beyond a segment");
    osprey_free(ctx);

    ctx = new_context();
    extent = chunk(global, 0, 64);
    source = chunk(global, 0, 4);
    target = chunk(global, 16, 8);
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &source, 1, 1);
    add_logical(ctx, 0x20, &target, 1, 1);
    seed_field(ctx, source, source.address);
    seed_homo(ctx, address(global, 0), address(global, 16), 16);
    CHECK(build_secondary(ctx), "CD08 unequal-width near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD08) == 0,
          "CD08 requires equal field widths");
    osprey_free(ctx);

    ctx = new_context();
    extent = chunk(global, 0, 64);
    source = chunk(global, 12, 4);
    target = chunk(global, 28, 4);
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &source, 1, 1);
    add_logical(ctx, 0x20, &target, 1, 1);
    seed_field(ctx, source, address(global, 0));
    seed_homo(ctx, address(global, 0), address(global, 16), 16);
    CHECK(build_secondary(ctx), "CD08 exact-end translation");
    CHECK(rule_count(ctx, OSPREY_RULE_CD08) == 2,
          "CD08 permits a field ending at the segment boundary");
    osprey_free(ctx);

    ctx = new_context();
    extent = chunk(global, 0, 64);
    source = chunk(global, 0, 4);
    target = chunk(global, 16, 4);
    OspreyChunk second_target = chunk(global, 32, 4);
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &source, 1, 1);
    add_logical(ctx, 0x20, &target, 1, 1);
    add_logical(ctx, 0x30, &second_target, 1, 1);
    seed_field(ctx, source, source.address);
    seed_homo(ctx, address(global, 0), address(global, 16), 16);
    seed_homo(ctx, address(global, 16), address(global, 32), 16);
    CHECK(build_secondary(ctx), "CD08 multi-round closure");
    CHECK(field_variable_id(ctx, &second_target, &second_target.address) !=
              UINT32_MAX && rule_count(ctx, OSPREY_RULE_CD08) >= 2,
          "CD08 propagates a field through successive segments");
    osprey_free(ctx);
}

static void test_cd10(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk value = chunk(global, 8, 4);
    OspreyChunk extent = chunk(global, 0, 32);
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &value, 1, 1);
    OspreyAddress first_base = address(global, 0);
    OspreyAddress second_base = address(global, 4);
    seed_field(ctx, value, first_base);
    seed_field(ctx, value, second_base);
    CHECK(build_secondary(ctx), "CD10 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CD10) == 2,
          "CD10 emits exactly two reverse factors for two bases");
    osprey_free(ctx);

    ctx = new_context();
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &value, 1, 1);
    seed_field(ctx, value, first_base);
    seed_field(ctx, value, first_base);
    CHECK(build_secondary(ctx), "CD10 same-base near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD10) == 0,
          "CD10 omits equal-base self-factors");
    osprey_free(ctx);

    ctx = new_context();
    add_extent(ctx, &extent);
    add_logical(ctx, 0x10, &value, 1, 1);
    seed_field(ctx, value, address(global, 0));
    seed_field(ctx, value, address(global, 4));
    seed_field(ctx, value, address(global, 8));
    CHECK(build_secondary(ctx), "CD10 three-base coverage");
    CHECK(rule_count(ctx, OSPREY_RULE_CD10) == 6,
          "CD10 emits both directions for every base pair");
    osprey_free(ctx);
}

static void test_cd11(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk pointer = chunk(global, 0, 8);
    OspreyChunk target = chunk(global, 16, 8);
    add_logical(ctx, 0x10, &pointer, 1, 1);
    add_logical(ctx, 0x20, &target, 1, 1);
    add_points_fact(ctx, pointer, target.address);
    CHECK(build_secondary(ctx), "CD11 positive");
    CHECK(rule_count(ctx, OSPREY_RULE_CD11) == 1,
          "CD11 emits the pointer-target implication");
    uint32_t pointer_primitive = chunk_variable_id(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, &pointer);
    uint32_t target_primitive = chunk_variable_id(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, &target);
    uint32_t pointer_var = variable_id(ctx, OSPREY_PRED_POINTER,
                                       &(OspreyVarPayload){
                                           .attached = {
                                               .chunk = pointer,
                                               .base = target.address,
                                           },
                                       });
    uint32_t ids[3] = { pointer_primitive, target_primitive, pointer_var };
    expect_factor(ctx, OSPREY_RULE_CD11, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 2,
                  ids, 3, "CD11 exact pointer and target roles");
    CHECK(pointer_var != UINT32_MAX, "CD11 interns the pointer head");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk narrow_target = chunk(global, 16, 4);
    OspreyChunk wide_target = chunk(global, 16, 8);
    OspreyChunk pointer_extent = chunk(global, 0, 24);
    add_extent(ctx, &pointer_extent);
    add_logical(ctx, 0x10, &pointer, 1, 1);
    add_logical(ctx, 0x20, &narrow_target, 1, 1);
    add_logical(ctx, 0x30, &wide_target, 1, 1);
    add_points_fact(ctx, pointer, narrow_target.address);
    CHECK(build_secondary(ctx), "CD11 multiple target widths");
    CHECK(rule_count(ctx, OSPREY_RULE_CD11) == 2,
          "CD11 retains each accessed target width witness");
    uint32_t pointer_id = chunk_variable_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                            &pointer);
    uint32_t narrow_target_id = chunk_variable_id(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, &narrow_target);
    uint32_t wide_target_id = chunk_variable_id(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, &wide_target);
    uint32_t narrow_pointer_id = variable_id(
        ctx, OSPREY_PRED_POINTER,
        &(OspreyVarPayload){ .attached = {
            .chunk = pointer, .base = narrow_target.address,
        }});
    uint32_t narrow_roles[3] = {
        pointer_id, narrow_target_id, narrow_pointer_id,
    };
    uint32_t wide_roles[3] = {
        pointer_id, wide_target_id, narrow_pointer_id,
    };
    expect_factor(ctx, OSPREY_RULE_CD11, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 2,
                  narrow_roles, 3, "CD11 narrow target role");
    expect_factor(ctx, OSPREY_RULE_CD11, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 2,
                  wide_roles, 3, "CD11 wide target role");
    osprey_free(ctx);

    ctx = new_context();
    OspreyRegionId stack = region(OSPREY_REGION_STACK_FUNCTION, 7);
    OspreyChunk stack_target = chunk(stack, target.address.offset, target.size);
    add_logical(ctx, 0x10, &pointer, 1, 1);
    add_logical(ctx, 0x20, &stack_target, 1, 1);
    add_points_fact(ctx, pointer, target.address);
    CHECK(build_secondary(ctx), "CD11 target-region mismatch");
    CHECK(rule_count(ctx, OSPREY_RULE_CD11) == 0,
          "CD11 requires the pointed-to target region");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &pointer, 1, 1);
    add_points_fact(ctx, pointer, target.address);
    CHECK(build_secondary(ctx), "CD11 missing-target-access near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD11) == 0,
          "CD11 requires target access");
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &pointer, 1, 1);
    add_points_fact(ctx, pointer, address(global, 0x1234));
    CHECK(build_secondary(ctx), "CD11 numeric-target near miss");
    CHECK(rule_count(ctx, OSPREY_RULE_CD11) == 0,
          "CD11 excludes untagged numeric targets");
    osprey_free(ctx);

    ctx = new_context();
    OspreyChunk self_pointer = chunk(global, 0, 8);
    add_logical(ctx, 0x10, &self_pointer, 1, 1);
    add_points_fact(ctx, self_pointer, self_pointer.address);
    CHECK(build_secondary(ctx), "CD11 self-target case");
    CHECK(rule_count(ctx, OSPREY_RULE_CD11) == 1,
          "CD11 retains a pointer whose target chunk is itself");
    uint32_t self_primitive = chunk_variable_id(
        ctx, OSPREY_PRED_PRIMITIVE_VAR, &self_pointer);
    uint32_t self_pointer_id = variable_id(
        ctx, OSPREY_PRED_POINTER,
        &(OspreyVarPayload){ .attached = {
            .chunk = self_pointer, .base = self_pointer.address,
        }});
    uint32_t self_roles[2] = { self_primitive, self_pointer_id };
    expect_factor(ctx, OSPREY_RULE_CD11, OSPREY_GRAPH_SECONDARY,
                  OSPREY_POTENTIAL_IMPLICATION, false, 0.8, 1,
                  self_roles, 2, "CD11 simplifies duplicate antecedents");
    osprey_free(ctx);
}

typedef OspreyContext *(*PermutationBuilder)(bool reverse);
typedef void (*RuleTest)(void);

typedef struct Stage3RuleCase {
    uint16_t rule;
    const char *name;
    RuleTest test;
} Stage3RuleCase;

static OspreyContext *permutation_context(uint16_t rule, bool reverse)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk a = chunk(global, 0, 8);
    OspreyChunk b = chunk(global, 8, 8);
    OspreyChunk c = chunk(global, 16, 8);
    OspreyStatus status;

    switch (rule) {
    case OSPREY_RULE_CA01:
        if (reverse) {
            add_logical(ctx, 0x20, &b, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x20, &b, 1, 1);
        }
        status = osprey_stage3_base(ctx);
        break;
    case OSPREY_RULE_CA02:
        if (reverse) {
            add_logical(ctx, 0x20, &b, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x20, &b, 1, 1);
        }
        status = osprey_stage3_base(ctx);
        break;
    case OSPREY_RULE_CA03: {
        OspreyChunk overlap = chunk(global, 4, 8);
        if (reverse) {
            add_logical(ctx, 0x20, &overlap, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x20, &overlap, 1, 1);
        }
        status = osprey_stage3_base(ctx);
        break;
    }
    case OSPREY_RULE_CA04:
        if (reverse) {
            add_logical(ctx, 0x20, &b, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x20, &b, 1, 1);
        }
        status = osprey_stage3_base(ctx);
        break;
    case OSPREY_RULE_CA05:
        if (reverse) {
            add_logical(ctx, 0x10, &c, 1, 1);
            add_logical(ctx, 0x10, &b, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x10, &b, 1, 1);
            add_logical(ctx, 0x10, &c, 1, 1);
        }
        status = osprey_stage3_base(ctx);
        break;
    case OSPREY_RULE_CA06:
        if (reverse) {
            add_logical(ctx, 0x20, &a, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x20, &a, 1, 1);
        }
        status = osprey_stage3_base(ctx);
        break;
    case OSPREY_RULE_CA07:
        if (reverse) {
            add_logical(ctx, 0x20, &b, 1, 4);
            add_logical(ctx, 0x10, &a, 1, 4);
        } else {
            add_logical(ctx, 0x10, &a, 1, 4);
            add_logical(ctx, 0x20, &b, 1, 4);
        }
        status = osprey_stage3_base(ctx);
        break;
    case OSPREY_RULE_CA08: {
        OspreyAddress base_zero = address(global, 0);
        OspreyAddress base_eight = address(global, 8);
        OspreyVarPayload first_field;
        OspreyVarPayload second_field;
        memset(&first_field, 0, sizeof(first_field));
        memset(&second_field, 0, sizeof(second_field));
        first_field.attached.chunk = a;
        first_field.attached.base = base_zero;
        second_field.attached.chunk = a;
        second_field.attached.base = base_eight;
        add_logical(ctx, 0x10, &a, 1, 1);
        OspreyChunk full_extent = chunk(global, 0, 16);
        add_extent(ctx, &full_extent);
        if (reverse) {
            osprey_intern_var(ctx, OSPREY_PRED_FIELD_OF, &second_field);
            osprey_intern_var(ctx, OSPREY_PRED_FIELD_OF, &first_field);
        } else {
            osprey_intern_var(ctx, OSPREY_PRED_FIELD_OF, &first_field);
            osprey_intern_var(ctx, OSPREY_PRED_FIELD_OF, &second_field);
        }
        status = osprey_stage3_base(ctx);
        break;
    }
    case OSPREY_RULE_CB01: {
        OspreyMayArrayFact first_fact;
        OspreyMayArrayFact second_fact;
        memset(&first_fact, 0, sizeof(first_fact));
        memset(&second_fact, 0, sizeof(second_fact));
        first_fact.start = a.address;
        first_fact.element_count = 1;
        first_fact.element_size = 8;
        first_fact.evidence_kind = OSPREY_MAY_ARRAY_CALLOC_GEOMETRY;
        first_fact.sample_support = 1;
        second_fact = first_fact;
        second_fact.start = b.address;
        if (reverse) {
            add_logical(ctx, 0x20, &b, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
            g_array_append_val(ctx->mayarray_facts, second_fact);
            g_array_append_val(ctx->mayarray_facts, first_fact);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x20, &b, 1, 1);
            g_array_append_val(ctx->mayarray_facts, first_fact);
            g_array_append_val(ctx->mayarray_facts, second_fact);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CB02:
        if (reverse) {
            add_logical(ctx, 0x10, &c, 1, 1);
            add_logical(ctx, 0x10, &b, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x10, &b, 1, 1);
            add_logical(ctx, 0x10, &c, 1, 1);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CB03: {
        OspreyChunk extent = chunk(global, 0, 24);
        add_extent(ctx, &extent);
        if (reverse) {
            seed_array(ctx, global, 8, 24, 8);
            seed_array(ctx, global, 0, 16, 8);
        } else {
            seed_array(ctx, global, 0, 16, 8);
            seed_array(ctx, global, 8, 24, 8);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CB04: {
        OspreyChunk extent = chunk(global, 0, 24);
        add_extent(ctx, &extent);
        if (reverse) {
            seed_array(ctx, global, 8, 24, 4);
            seed_array(ctx, global, 0, 16, 8);
        } else {
            seed_array(ctx, global, 0, 16, 8);
            seed_array(ctx, global, 8, 24, 4);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CB05: {
        OspreyChunk scalar = chunk(global, 8, 8);
        OspreyChunk extent = chunk(global, 0, 32);
        add_extent(ctx, &extent);
        if (reverse) {
            (void)seed_scalar(ctx, &scalar);
            (void)seed_array(ctx, global, 0, 32, 8);
        } else {
            (void)seed_array(ctx, global, 0, 32, 8);
            (void)seed_scalar(ctx, &scalar);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CB06: {
        OspreyChunk extent = chunk(global, 0, 16);
        add_logical(ctx, 0x10, &a, 1, 1);
        add_extent(ctx, &extent);
        status = osprey_stage3_base(ctx);
        if (status == OSPREY_OK) {
            OspreyVar malformed;
            memset(&malformed, 0, sizeof(malformed));
            malformed.id = ctx->graph->vars->len;
            malformed.kind = OSPREY_PRED_ARRAY;
            malformed.payload.segment.a1 = address(global, 0);
            malformed.payload.segment.a2 = address(global, 4);
            malformed.payload.segment.size = 8;
            g_array_append_val(ctx->graph->vars, malformed);
            status = osprey_stage3_secondary(ctx);
        }
        break;
    }
    case OSPREY_RULE_CB07: {
        OspreyBaseFact first_base;
        OspreyBaseFact second_base;
        memset(&first_base, 0, sizeof(first_base));
        memset(&second_base, 0, sizeof(second_base));
        first_base.pc = 0x10;
        first_base.chunk = a;
        first_base.base = a.address;
        second_base = first_base;
        second_base.chunk = b;
        second_base.base = b.address;
        if (reverse) {
            add_logical(ctx, 0x10, &b, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
            g_array_append_val(ctx->base_facts, second_base);
            g_array_append_val(ctx->base_facts, first_base);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x10, &b, 1, 1);
            g_array_append_val(ctx->base_facts, first_base);
            g_array_append_val(ctx->base_facts, second_base);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CB08:
        if (reverse) {
            add_logical(ctx, 0x10, &c, 3, 1);
            add_logical(ctx, 0x10, &b, 3, 1);
            add_logical(ctx, 0x10, &a, 3, 1);
        } else {
            add_logical(ctx, 0x10, &a, 3, 1);
            add_logical(ctx, 0x10, &b, 3, 1);
            add_logical(ctx, 0x10, &c, 3, 1);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CB09: {
        OspreyBaseFact first_base;
        OspreyBaseFact second_base;
        memset(&first_base, 0, sizeof(first_base));
        memset(&second_base, 0, sizeof(second_base));
        first_base.pc = 0x10;
        first_base.chunk = a;
        first_base.base = a.address;
        second_base = first_base;
        second_base.chunk = b;
        second_base.base = b.address;
        if (reverse) {
            add_logical(ctx, 0x10, &b, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
            g_array_append_val(ctx->base_facts, second_base);
            g_array_append_val(ctx->base_facts, first_base);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x10, &b, 1, 1);
            g_array_append_val(ctx->base_facts, first_base);
            g_array_append_val(ctx->base_facts, second_base);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CC01: {
        OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x801);
        add_allocation(ctx, heap.site_offset, 0);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CC02: {
        OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x802);
        if (reverse) {
            add_allocation(ctx, heap.site_offset, 48);
            add_allocation(ctx, heap.site_offset, 16);
            add_allocation(ctx, heap.site_offset, 0);
        } else {
            add_allocation(ctx, heap.site_offset, 0);
            add_allocation(ctx, heap.site_offset, 16);
            add_allocation(ctx, heap.site_offset, 48);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CC03: {
        OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x803);
        OspreyChunk value = chunk(heap, 8, 8);
        add_allocation(ctx, heap.site_offset, 32);
        add_logical(ctx, 0x10, &value, 1, 1);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CC04:
    case OSPREY_RULE_CC05: {
        OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x804);
        if (reverse) {
            seed_heap_unfoldable(ctx, heap, 24);
            seed_heap_unfoldable(ctx, heap, 8);
            seed_heap_unfoldable(ctx, heap, 16);
        } else {
            seed_heap_unfoldable(ctx, heap, 8);
            seed_heap_unfoldable(ctx, heap, 16);
            seed_heap_unfoldable(ctx, heap, 24);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CC06: {
        OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x805);
        add_allocation(ctx, heap.site_offset, 32);
        seed_array(ctx, heap, 0, 32, 8);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CC07: {
        OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x806);
        OspreyChunk value = chunk(heap, 12, 4);
        OspreyChunk folded = chunk(heap, 8, 4);
        add_allocation(ctx, heap.site_offset, 16);
        CHECK(osprey_candidate_select(ctx, NULL, 0) == OSPREY_OK,
              "CC07 permutation extent catalog");
        seed_primitive(ctx, value);
        seed_heap_unfoldable(ctx, heap, 8);
        seed_heap_foldable(ctx, heap, 4);
        seed_primitive(ctx, folded);
        status = osprey_relations_build(ctx);
        if (status == OSPREY_OK) {
            uint32_t primitive = chunk_variable_id(ctx,
                OSPREY_PRED_PRIMITIVE_VAR, &value);
            uint32_t folded_id = chunk_variable_id(ctx,
                OSPREY_PRED_PRIMITIVE_VAR, &folded);
            uint32_t unfoldable = heap_fold_variable_id(
                ctx, OSPREY_PRED_UNFOLDABLE_HEAP, heap, 8);
            uint32_t foldable = heap_fold_variable_id(
                ctx, OSPREY_PRED_FOLDABLE_HEAP, heap, 4);
            status = osprey_compile_cc07(ctx, primitive, unfoldable,
                                         foldable, folded_id);
        }
        break;
    }
    case OSPREY_RULE_CD01: {
        if (reverse) {
            add_copy_fact(ctx, chunk(global, 16, 8), chunk(global, 116, 8));
            add_copy_fact(ctx, chunk(global, 0, 8), chunk(global, 100, 8));
        } else {
            add_copy_fact(ctx, chunk(global, 0, 8), chunk(global, 100, 8));
            add_copy_fact(ctx, chunk(global, 16, 8), chunk(global, 116, 8));
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CD02:
        populate_cd02(ctx, reverse);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CD03:
        populate_cd03(ctx, reverse, 16);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CD04: {
        OspreyChunk extent = chunk(global, 0, 48);
        OspreyChunk starts[4] = {
            chunk(global, 0, 1), chunk(global, 4, 1),
            chunk(global, 32, 1), chunk(global, 36, 1)
        };
        add_extent(ctx, &extent);
        for (guint i = 0; i < G_N_ELEMENTS(starts); i++) {
            add_logical(ctx, 0x10 + i, &starts[i], 1, 1);
        }
        if (reverse) {
            seed_homo(ctx, address(global, 4), address(global, 36), 8);
            seed_homo(ctx, address(global, 0), address(global, 32), 16);
        } else {
            seed_homo(ctx, address(global, 0), address(global, 32), 16);
            seed_homo(ctx, address(global, 4), address(global, 36), 8);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CD05: {
        OspreyChunk extent = chunk(global, 0, 32);
        OspreyChunk first = chunk(global, 4, 4);
        OspreyChunk second = chunk(global, 20, 8);
        add_extent(ctx, &extent);
        if (reverse) {
            add_logical(ctx, 0x20, &second, 1, 1);
            add_logical(ctx, 0x10, &first, 1, 1);
        } else {
            add_logical(ctx, 0x10, &first, 1, 1);
            add_logical(ctx, 0x20, &second, 1, 1);
        }
        seed_homo(ctx, address(global, 0), address(global, 16), 16);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CD06:
        populate_cd06(ctx, reverse, true, false);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CD07: {
        OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x807);
        OspreyChunk value = chunk(heap, 4, 4);
        add_allocation(ctx, heap.site_offset, 16);
        add_logical(ctx, 0x10, &value, 1, 1);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CD08: {
        OspreyChunk extent = chunk(global, 0, 64);
        OspreyChunk source = chunk(global, 0, 4);
        OspreyChunk target = chunk(global, 16, 4);
        add_extent(ctx, &extent);
        if (reverse) {
            add_logical(ctx, 0x20, &target, 1, 1);
            add_logical(ctx, 0x10, &source, 1, 1);
        } else {
            add_logical(ctx, 0x10, &source, 1, 1);
            add_logical(ctx, 0x20, &target, 1, 1);
        }
        seed_field(ctx, source, source.address);
        seed_homo(ctx, address(global, 0), address(global, 16), 16);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CD10: {
        OspreyChunk extent = chunk(global, 0, 32);
        OspreyChunk value = chunk(global, 8, 4);
        add_extent(ctx, &extent);
        add_logical(ctx, 0x10, &value, 1, 1);
        if (reverse) {
            seed_field(ctx, value, address(global, 4));
            seed_field(ctx, value, address(global, 0));
        } else {
            seed_field(ctx, value, address(global, 0));
            seed_field(ctx, value, address(global, 4));
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CD11: {
        OspreyChunk pointer = chunk(global, 0, 8);
        OspreyChunk target = chunk(global, 16, 8);
        if (reverse) {
            add_logical(ctx, 0x20, &target, 1, 1);
            add_logical(ctx, 0x10, &pointer, 1, 1);
        } else {
            add_logical(ctx, 0x10, &pointer, 1, 1);
            add_logical(ctx, 0x20, &target, 1, 1);
        }
        add_points_fact(ctx, pointer, target.address);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    default:
        status = OSPREY_INVALID_GRAPH;
        break;
    }
    CHECK(status == OSPREY_OK, "permutation fixture builds");
    return ctx;
}

static OspreyContext *permutation_near_miss_context(uint16_t rule,
                                                     bool reverse)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
    OspreyChunk a = chunk(global, 0, 8);
    OspreyChunk b = chunk(global, 8, 8);
    OspreyStatus status;

    switch (rule) {
    case OSPREY_RULE_CA01:
    case OSPREY_RULE_CA04:
        status = osprey_stage3_base(ctx);
        break;
    case OSPREY_RULE_CA02: {
        OspreyChunk gap = chunk(global, 17, 8);
        if (reverse) {
            add_logical(ctx, 0x20, &gap, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x20, &gap, 1, 1);
        }
        status = osprey_stage3_base(ctx);
        break;
    }
    case OSPREY_RULE_CA03:
        if (reverse) {
            add_logical(ctx, 0x20, &b, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x20, &b, 1, 1);
        }
        status = osprey_stage3_base(ctx);
        break;
    case OSPREY_RULE_CA05:
        if (reverse) {
            add_logical(ctx, 0x20, &b, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x20, &b, 1, 1);
        }
        status = osprey_stage3_base(ctx);
        break;
    case OSPREY_RULE_CA06:
    case OSPREY_RULE_CA07:
        if (reverse) {
            add_logical(ctx, 0x10, &b, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x10, &b, 1, 1);
        }
        status = osprey_stage3_base(ctx);
        break;
    case OSPREY_RULE_CA08:
        add_logical(ctx, 0x10, &a, 1, 1);
        status = osprey_stage3_base(ctx);
        break;
    case OSPREY_RULE_CB01:
        add_logical(ctx, 0x10, &a, 1, 1);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CB02:
        add_logical(ctx, 0x10, &a, 1, 1);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CB03: {
        OspreyChunk extent = chunk(global, 0, 24);
        add_extent(ctx, &extent);
        if (reverse) {
            (void)seed_array(ctx, global, 1, 16, 8);
            (void)seed_array(ctx, global, 0, 16, 8);
        } else {
            (void)seed_array(ctx, global, 0, 16, 8);
            (void)seed_array(ctx, global, 1, 16, 8);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CB04: {
        OspreyChunk extent = chunk(global, 0, 24);
        add_extent(ctx, &extent);
        if (reverse) {
            (void)seed_array(ctx, global, 4, 11, 4);
            (void)seed_array(ctx, global, 0, 8, 8);
        } else {
            (void)seed_array(ctx, global, 0, 8, 8);
            (void)seed_array(ctx, global, 4, 11, 4);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CB05: {
        OspreyChunk extent = chunk(global, 0, 32);
        OspreyChunk at_hi = chunk(global, 32, 8);
        add_extent(ctx, &extent);
        (void)seed_array(ctx, global, 0, 32, 8);
        (void)seed_scalar(ctx, &at_hi);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CB06:
        add_logical(ctx, 0x10, &a, 1, 1);
        (void)seed_array(ctx, global, 0, 8, 8);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CB07: {
        OspreyBaseFact base;
        memset(&base, 0, sizeof(base));
        base.pc = 0x20;
        base.chunk = a;
        base.base = a.address;
        add_logical(ctx, 0x10, &a, 1, 1);
        add_logical(ctx, 0x10, &b, 1, 1);
        g_array_append_val(ctx->base_facts, base);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CB08:
        add_logical(ctx, 0x10, &a, 3, 1);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CB09:
        if (reverse) {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
        } else {
            add_logical(ctx, 0x10, &a, 1, 1);
            add_logical(ctx, 0x10, &a, 1, 1);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CC01: {
        OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x901);
        add_allocation(ctx, heap.site_offset, 0);
        add_allocation(ctx, heap.site_offset, 16);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CC02: {
        OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x902);
        add_allocation(ctx, heap.site_offset, 16);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CC03: {
        OspreyChunk value = chunk(global, 0, 8);
        add_logical(ctx, 0x10, &value, 1, 1);
        status = osprey_stage3_base(ctx);
        break;
    }
    case OSPREY_RULE_CC04:
    case OSPREY_RULE_CC05: {
        OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x904);
        seed_heap_unfoldable(ctx, heap, 8);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CC06: {
        OspreyRegionId global = region(OSPREY_REGION_GLOBAL, 0);
        OspreyChunk extent = chunk(global, 0, 32);
        add_extent(ctx, &extent);
        seed_array(ctx, global, 0, 32, 8);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CC07: {
        OspreyRegionId heap = region(OSPREY_REGION_HEAP_SITE, 0x906);
        OspreyChunk value = chunk(heap, 11, 4);
        OspreyChunk folded = chunk(heap, 11, 4);
        seed_primitive(ctx, value);
        seed_heap_unfoldable(ctx, heap, 8);
        seed_heap_foldable(ctx, heap, 4);
        seed_primitive(ctx, folded);
        status = osprey_stage3_base(ctx);
        break;
    }
    case OSPREY_RULE_CD01:
        add_copy_fact(ctx, chunk(global, 0, 8), chunk(global, 100, 8));
        add_copy_fact(ctx, chunk(global, 16, 8), chunk(global, 117, 8));
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CD02:
        populate_cd02(ctx, reverse);
        /* Replace the second target with a non-corresponding pointer only by
         * omitting the second point witness. */
        if (ctx->points_facts->len > 1) {
            g_array_set_size(ctx->points_facts, 1);
        }
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CD03:
        populate_cd03(ctx, reverse, 17);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CD04: {
        OspreyChunk extent = chunk(global, 0, 48);
        OspreyChunk starts[4] = {
            chunk(global, 0, 1), chunk(global, 4, 1),
            chunk(global, 32, 1), chunk(global, 37, 1)
        };
        add_extent(ctx, &extent);
        for (guint i = 0; i < G_N_ELEMENTS(starts); i++) {
            add_logical(ctx, 0x10 + i, &starts[i], 1, 1);
        }
        seed_homo(ctx, address(global, 0), address(global, 32), 16);
        seed_homo(ctx, address(global, 4), address(global, 37), 8);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CD05: {
        OspreyChunk extent = chunk(global, 0, 32);
        OspreyChunk first = chunk(global, 4, 4);
        OspreyChunk second = chunk(global, 20, 4);
        add_extent(ctx, &extent);
        add_logical(ctx, 0x10, &first, 1, 1);
        add_logical(ctx, 0x20, &second, 1, 1);
        seed_homo(ctx, address(global, 0), address(global, 16), 16);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CD06:
        populate_cd06(ctx, reverse, false, false);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    case OSPREY_RULE_CD07: {
        OspreyChunk extent = chunk(global, 0, 16);
        OspreyChunk value = chunk(global, 4, 4);
        add_extent(ctx, &extent);
        add_logical(ctx, 0x10, &value, 1, 1);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CD08: {
        OspreyChunk extent = chunk(global, 0, 64);
        OspreyChunk source = chunk(global, 15, 4);
        OspreyChunk target = chunk(global, 31, 4);
        add_extent(ctx, &extent);
        add_logical(ctx, 0x10, &source, 1, 1);
        add_logical(ctx, 0x20, &target, 1, 1);
        seed_field(ctx, source, address(global, 0));
        seed_homo(ctx, address(global, 0), address(global, 16), 16);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CD10: {
        OspreyChunk extent = chunk(global, 0, 32);
        OspreyChunk value = chunk(global, 8, 4);
        add_extent(ctx, &extent);
        add_logical(ctx, 0x10, &value, 1, 1);
        seed_field(ctx, value, address(global, 0));
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    case OSPREY_RULE_CD11: {
        OspreyChunk pointer = chunk(global, 0, 8);
        OspreyChunk target = chunk(global, 16, 8);
        add_logical(ctx, 0x10, &pointer, 1, 1);
        add_points_fact(ctx, pointer, target.address);
        status = build_secondary(ctx) ? OSPREY_OK : ctx->last_status;
        break;
    }
    default:
        status = OSPREY_INVALID_GRAPH;
        break;
    }
    CHECK(status == OSPREY_OK, "near-miss permutation fixture builds");
    return ctx;
}

static void test_rule_permutations(const Stage3RuleCase *cases,
                                    guint case_count)
{
    for (guint i = 0; i < case_count; i++) {
        OspreyContext *forward = permutation_context(cases[i].rule, false);
        OspreyContext *reverse = permutation_context(cases[i].rule, true);
        CHECK(variable_sets_equal(forward, reverse),
              cases[i].name);
        CHECK(candidate_accounting_equal(forward->graph, reverse->graph),
              cases[i].name);
        CHECK(rule_factor_sets_equal(forward, reverse, cases[i].rule),
              cases[i].name);
        osprey_free(reverse);
        osprey_free(forward);
    }
}

static const Stage3RuleCase stage3_rule_cases[] = {
    { OSPREY_RULE_CA01, "CA01", test_ca01 },
    { OSPREY_RULE_CA02, "CA02", test_ca02 },
    { OSPREY_RULE_CA03, "CA03", test_ca03 },
    { OSPREY_RULE_CA04, "CA04", test_ca04 },
    { OSPREY_RULE_CA05, "CA05", test_ca05 },
    { OSPREY_RULE_CA06, "CA06", test_ca06 },
    { OSPREY_RULE_CA07, "CA07", test_ca07 },
    { OSPREY_RULE_CA08, "CA08", test_ca08 },
    { OSPREY_RULE_CB01, "CB01", test_cb01 },
    { OSPREY_RULE_CB02, "CB02", test_cb02 },
    { OSPREY_RULE_CB03, "CB03", test_cb03 },
    { OSPREY_RULE_CB04, "CB04", test_cb04 },
    { OSPREY_RULE_CB05, "CB05", test_cb05 },
    { OSPREY_RULE_CB06, "CB06", test_cb06 },
    { OSPREY_RULE_CB07, "CB07", test_cb07 },
    { OSPREY_RULE_CB08, "CB08", test_cb08 },
    { OSPREY_RULE_CB09, "CB09", test_cb09 },
    { OSPREY_RULE_CC01, "CC01", test_cc01 },
    { OSPREY_RULE_CC02, "CC02", test_cc02 },
    { OSPREY_RULE_CC03, "CC03", test_cc03 },
    { OSPREY_RULE_CC04, "CC04", test_cc04 },
    { OSPREY_RULE_CC05, "CC05", test_cc05 },
    { OSPREY_RULE_CC06, "CC06", test_cc06 },
    { OSPREY_RULE_CC07, "CC07", test_cc07 },
    { OSPREY_RULE_CD01, "CD01", test_cd01 },
    { OSPREY_RULE_CD02, "CD02", test_cd02 },
    { OSPREY_RULE_CD03, "CD03", test_cd03 },
    { OSPREY_RULE_CD04, "CD04", test_cd04 },
    { OSPREY_RULE_CD05, "CD05", test_cd05 },
    { OSPREY_RULE_CD06, "CD06", test_cd06 },
    { OSPREY_RULE_CD07, "CD07", test_cd07 },
    { OSPREY_RULE_CD08, "CD08", test_cd08 },
    { OSPREY_RULE_CD10, "CD10", test_cd10 },
    { OSPREY_RULE_CD11, "CD11", test_cd11 },
};

static void test_near_miss_permutations(void)
{
    for (guint i = 0; i < G_N_ELEMENTS(stage3_rule_cases); i++) {
        OspreyContext *forward = permutation_near_miss_context(
            stage3_rule_cases[i].rule, false);
        OspreyContext *reverse = permutation_near_miss_context(
            stage3_rule_cases[i].rule, true);
        CHECK(variable_sets_equal(forward, reverse),
              stage3_rule_cases[i].name);
        CHECK(candidate_accounting_equal(forward->graph, reverse->graph),
              stage3_rule_cases[i].name);
        CHECK(rule_factor_sets_equal(forward, reverse,
                                     stage3_rule_cases[i].rule),
              stage3_rule_cases[i].name);
        osprey_free(reverse);
        osprey_free(forward);
    }
}

static void validate_rule_registry(void)
{
    bool seen[OSPREY_RULE_COUNT];
    memset(seen, 0, sizeof(seen));
    CHECK(G_N_ELEMENTS(stage3_rule_cases) == 34,
          "exactly 34 CA/CB/CC/CD cases are registered");
    for (guint i = 0; i < G_N_ELEMENTS(stage3_rule_cases); i++) {
        uint16_t rule = stage3_rule_cases[i].rule;
        CHECK(rule >= OSPREY_RULE_CA01 && rule <= OSPREY_RULE_CD11,
              "registered CA/CD code is in range");
        CHECK(!seen[rule], "registered CA/CD codes are unique");
        seen[rule] = true;
    }
    for (uint16_t rule = OSPREY_RULE_CA01;
         rule <= OSPREY_RULE_CD11; rule++) {
        CHECK(seen[rule], "every CA/CD code is registered");
    }
}

int main(void)
{
    validate_rule_registry();
    for (guint i = 0; i < G_N_ELEMENTS(stage3_rule_cases); i++) {
        registered++;
        stage3_rule_cases[i].test();
        executed++;
    }
    test_rule_permutations(stage3_rule_cases,
                           G_N_ELEMENTS(stage3_rule_cases));
    test_near_miss_permutations();
    CHECK(registered == executed, "every CA/CB/CC/CD rule row executed");
    if (failures != 0 || registered != executed) {
        fprintf(stderr, "FAIL stage3_rules (%u failures, %u/%u)\n",
                failures, executed, registered);
        return EXIT_FAILURE;
    }
    printf("PASS stage3_rules (%u/%u)\n", executed, registered);
    return EXIT_SUCCESS;
}
