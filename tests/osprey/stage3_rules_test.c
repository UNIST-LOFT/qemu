/* Stage 3.3 primitive/scalar/array rule tests. */

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

static void add_extent(OspreyContext *ctx, const OspreyChunk *value)
{
    OspreyAccessFact access;
    memset(&access, 0, sizeof(access));
    access.chunk = *value;
    access.dynamic_count = 1;
    access.sample_support = 1;
    g_array_append_val(ctx->access_facts, access);
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
    FILE *stream = tmpfile();
    CHECK(stream != NULL, "CB03 permutation dump file");
    if (stream == NULL) {
        osprey_free(ctx);
        return g_strdup("");
    }
    CHECK(osprey_graph_dump_file(ctx, stream), "CB03 permutation dump");
    fflush(stream);
    fseek(stream, 0, SEEK_END);
    long length = ftell(stream);
    CHECK(length >= 0, "CB03 permutation dump length");
    rewind(stream);
    char *text = g_malloc((size_t)(length < 0 ? 0 : length) + 1);
    size_t actual = length < 0 ? 0 : fread(text, 1, (size_t)length, stream);
    text[actual] = '\0';
    fclose(stream);
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
    osprey_free(ctx);

    ctx = new_context();
    CHECK(build_base(ctx), "CA01 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CA01) == 0,
          "CA01 has no witness without Access");
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
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical_value(ctx, 0x20, chunk(global, 17, 8), 1, 1);
    CHECK(build_base(ctx), "CA02 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CA02) == 0,
          "CA02 rejects a one-byte gap");
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
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    fact.element_count = 0;
    g_array_append_val(ctx->mayarray_facts, fact);
    CHECK(osprey_stage3_base(ctx) == OSPREY_GRAPH_ARITHMETIC,
          "CB01 rejects zero geometry");
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
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 3, 1);
    add_logical(ctx, 0x10, &b, 3, 1);
    CHECK(build_secondary(ctx), "CB08 tied addresses");
    CHECK(rule_count(ctx, OSPREY_RULE_CB08) == 2,
          "CB08 retains every R07 maximum address");
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
    osprey_free(ctx);

    ctx = new_context();
    add_logical(ctx, 0x10, &a, 1, 1);
    add_logical_value(ctx, 0x10, chunk(global, 0, 8), 1, 1);
    CHECK(build_secondary(ctx), "CB09 one-condition-off");
    CHECK(rule_count(ctx, OSPREY_RULE_CB09) == 0,
          "CB09 rejects equal starts");
    osprey_free(ctx);
}

int main(void)
{
    RUN(test_ca01);
    RUN(test_ca02);
    RUN(test_ca03);
    RUN(test_ca04);
    RUN(test_ca05);
    RUN(test_ca06);
    RUN(test_ca07);
    RUN(test_ca08);
    RUN(test_cb01);
    RUN(test_cb02);
    RUN(test_cb03);
    RUN(test_cb04);
    RUN(test_cb05);
    RUN(test_cb06);
    RUN(test_cb07);
    RUN(test_cb08);
    RUN(test_cb09);
    CHECK(registered == executed, "every CA/CB rule row executed");
    if (failures != 0 || registered != executed) {
        fprintf(stderr, "FAIL stage3_rules (%u failures, %u/%u)\n",
                failures, executed, registered);
        return EXIT_FAILURE;
    }
    printf("PASS stage3_rules (%u/%u)\n", executed, registered);
    return EXIT_SUCCESS;
}
