#include "osprey.h"
#include "osprey-internal.h"
#include "stage5_bp_reference.h"

#include <float.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned failures;
static unsigned registered;
static unsigned executed;

/* Ten policy-stable rounds stop before exact tree arithmetic converges.  The
 * fixed 2,000-case corpus measured a maximum error of 0x1.0cd00168p-24;
 * retain a decimal bound with margin while keeping the required stop rule. */
#define OSPREY_BP_FOREST_ORACLE_TOL 1e-7

#define CHECK(condition, message) do {                                      \
    if (!(condition)) {                                                      \
        fprintf(stderr, "FAIL: %s (line %d)\n", (message), __LINE__);      \
        failures++;                                                          \
    }                                                                            \
} while (0)

#define RUN(test) do {                                                       \
    registered++;                                                            \
    test();                                                                  \
    executed++;                                                              \
} while (0)

static OspreyConfig bp_config(void)
{
    OspreyConfig config;
    memset(&config, 0, sizeof(config));
    config.enabled = true;
    config.shared_bytes = 1u << 20;
    config.max_facts = 1024;
    config.max_chunks_per_region = 128;
    config.max_candidates_per_kind_region = 4096;
    config.max_variables = 1024;
    config.max_factors = 4096;
    config.max_exact_clique_vars = 20;
    config.max_exact_table_bytes = 1u << 20;
    config.max_bp_table_bytes = 1u << 20;
    config.report_threshold = 0.5;
    return config;
}

static OspreyRegionId make_region(OspreyRegionKind kind, uint64_t site)
{
    OspreyRegionId region;
    memset(&region, 0, sizeof(region));
    region.kind = kind;
    region.site_offset = site;
    return region;
}

static OspreyChunk make_chunk(OspreyRegionId region, int64_t offset,
                              uint64_t size)
{
    OspreyChunk chunk;
    memset(&chunk, 0, sizeof(chunk));
    chunk.address.region = region;
    chunk.address.offset = offset;
    chunk.size = size;
    return chunk;
}

static OspreyContext *new_context_with_config(const OspreyConfig *config)
{
    OspreyContext *ctx = osprey_new(config);
    if (ctx != NULL) ctx->graph = osprey_graph_new();
    return ctx;
}

static OspreyContext *new_context(void)
{
    OspreyConfig config = bp_config();
    return new_context_with_config(&config);
}

static uint32_t add_primitive(OspreyContext *ctx, OspreyRegionId region,
                              int64_t offset)
{
    OspreyVarPayload payload;
    OspreyInternResult result;
    memset(&payload, 0, sizeof(payload));
    payload.chunk = make_chunk(region, offset, 8);
    result = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &payload);
    CHECK(result.id != UINT32_MAX, "primitive variable inserted");
    return result.id;
}

static bool add_prior(OspreyContext *ctx, uint32_t id, double probability)
{
    OspreyFactorResult result = osprey_factor_add_prior(
        ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, false, probability, id);
    CHECK(result.status == OSPREY_OK, "base prior inserted");
    return result.status == OSPREY_OK;
}

static bool add_secondary(OspreyContext *ctx, uint16_t rule,
                          const uint32_t *ids, uint32_t antecedents,
                          uint32_t head)
{
    OspreyFactorResult result = osprey_factor_add_implication(
        ctx, rule, OSPREY_GRAPH_SECONDARY, false, 0.8, ids, antecedents,
        head);
    CHECK(result.status == OSPREY_OK, "secondary implication inserted");
    return result.status == OSPREY_OK;
}

static void set_seed(OspreyContext *ctx, uint32_t id, double belief)
{
    OspreyVar *variable = &g_array_index(ctx->graph->vars, OspreyVar, id);
    variable->belief = belief;
    variable->belief_valid = 1;
}

static uint32_t local_for_offset(const OspreyContext *ctx,
                                 const OspreyBpGraph *graph, int64_t offset)
{
    for (guint local = 0; local < graph->vars->len; local++) {
        const OspreyBpVarRef *ref = &g_array_index(graph->vars,
                                                   OspreyBpVarRef, local);
        const OspreyVar *variable = &g_array_index(
            ctx->graph->vars, OspreyVar, ref->graph_var_id);
        if (variable->kind == OSPREY_PRED_PRIMITIVE_VAR &&
            variable->payload.chunk.address.offset == offset) return local;
    }
    return UINT32_MAX;
}

static char *dump_graph(const OspreyContext *ctx, const OspreyBpGraph *graph)
{
    char *data = NULL;
    size_t length = 0;
    FILE *out = open_memstream(&data, &length);
    if (out == NULL) return NULL;
    if (!osprey_bp_graph_dump_file(ctx, graph, out) || fclose(out) != 0) {
        free(data);
        return NULL;
    }
    return data;
}

static OspreyBpMessages graph_messages(OspreyBpGraph *graph)
{
    OspreyBpMessages messages;
    memset(&messages, 0, sizeof(messages));
    if (graph != NULL) {
        messages.vf_current = graph->msg_vf_current;
        messages.vf_next = graph->msg_vf_next;
        messages.fv_current = graph->msg_fv_current;
        messages.fv_next = graph->msg_fv_next;
        messages.value_count = graph->message_values;
    }
    return messages;
}

static bool message_pair_close(const double *left, const double *right)
{
    for (unsigned i = 0; i < 2; i++) {
        if (left[i] == -INFINITY || right[i] == -INFINITY) {
            if (left[i] != right[i]) return false;
        } else if (!isfinite(left[i]) || !isfinite(right[i]) ||
                   fabs(left[i] - right[i]) > 1e-12) {
            return false;
        }
    }
    return true;
}

static void set_log_probability_pair(double *pair, double probability)
{
    pair[0] = probability == 1.0 ? -INFINITY : log(1.0 - probability);
    pair[1] = probability == 0.0 ? -INFINITY : log(probability);
}

static bool compare_round_with_reference(const OspreyContext *ctx,
                                         OspreyBpGraph *graph,
                                         OspreyStatus expected_status)
{
    OspreyBpMessages production;
    OspreyBpMessages reference;
    OspreyBpRoundStats stats;
    double *vf_current;
    double *fv_current;
    double *vf_next;
    double *fv_next;
    OspreyStatus production_status;
    OspreyStatus reference_status;
    bool matches = true;

    if (ctx == NULL || graph == NULL || graph->message_values == 0 ||
        graph->message_values > SIZE_MAX / sizeof(double)) return false;
    vf_current = g_new(double, (size_t)graph->message_values);
    fv_current = g_new(double, (size_t)graph->message_values);
    vf_next = g_new(double, (size_t)graph->message_values);
    fv_next = g_new(double, (size_t)graph->message_values);
    memcpy(vf_current, graph->msg_vf_current,
           (size_t)graph->message_values * sizeof(double));
    memcpy(fv_current, graph->msg_fv_current,
           (size_t)graph->message_values * sizeof(double));
    for (uint64_t i = 0; i < graph->message_values; i++) {
        vf_next[(size_t)i] = NAN;
        fv_next[(size_t)i] = NAN;
    }
    production = graph_messages(graph);
    reference.vf_current = vf_current;
    reference.vf_next = vf_next;
    reference.fv_current = fv_current;
    reference.fv_next = fv_next;
    reference.value_count = graph->message_values;
    production_status = osprey_bp_compute_round(ctx, graph, &production,
                                                &stats);
    reference_status = stage5_bp_reference_compute_round(ctx, graph,
                                                          &reference);
    if (memcmp(graph->msg_vf_current, vf_current,
               (size_t)graph->message_values * sizeof(double)) != 0 ||
        memcmp(graph->msg_fv_current, fv_current,
               (size_t)graph->message_values * sizeof(double)) != 0) {
        matches = false;
    }
    for (uint64_t i = 0; i < (uint64_t)graph->vars->len * 2u; i++) {
        if (!isnan(graph->beliefs[(size_t)i])) matches = false;
    }
    if (production_status != expected_status ||
        reference_status != expected_status) {
        matches = false;
    }
    if (production_status == OSPREY_OK && reference_status == OSPREY_OK) {
        if (stats.variable_messages != graph->edges->len ||
            stats.factor_messages != graph->edges->len) matches = false;
        for (guint edge_id = 0; edge_id < graph->edges->len; edge_id++) {
            size_t index = (size_t)edge_id * 2u;
            if (!message_pair_close(&production.vf_next[index],
                                    &reference.vf_next[index]) ||
                !message_pair_close(&production.fv_next[index],
                                    &reference.fv_next[index])) {
                matches = false;
                break;
            }
        }
    } else {
        for (uint64_t i = 0; i < graph->message_values; i++) {
            if (!isnan(production.vf_next[(size_t)i]) ||
                !isnan(production.fv_next[(size_t)i]) ||
                !isnan(reference.vf_next[(size_t)i]) ||
                !isnan(reference.fv_next[(size_t)i])) {
                matches = false;
                break;
            }
        }
    }
    g_free(vf_current);
    g_free(fv_current);
    g_free(vf_next);
    g_free(fv_next);
    return matches;
}

static bool add_implication_probability(OspreyContext *ctx, uint16_t rule,
                                        uint8_t stage, bool negative,
                                        double probability,
                                        const uint32_t *antecedents,
                                        uint32_t count, uint32_t head)
{
    OspreyFactorResult result = osprey_factor_add_implication(
        ctx, rule, stage, negative, probability, antecedents, count, head);
    CHECK(result.status == OSPREY_OK, "implication inserted");
    return result.status == OSPREY_OK;
}

static uint32_t add_scalar(OspreyContext *ctx, OspreyRegionId region,
                           int64_t offset)
{
    OspreyVarPayload payload;
    OspreyInternResult result;
    memset(&payload, 0, sizeof(payload));
    payload.chunk = make_chunk(region, offset, 8);
    result = osprey_intern_var(ctx, OSPREY_PRED_SCALAR, &payload);
    CHECK(result.id != UINT32_MAX, "scalar variable inserted");
    return result.id;
}

static uint32_t add_field(OspreyContext *ctx, OspreyRegionId region,
                          int64_t offset, int64_t base_offset)
{
    OspreyVarPayload payload;
    OspreyInternResult result;
    memset(&payload, 0, sizeof(payload));
    payload.attached.chunk = make_chunk(region, offset, 8);
    payload.attached.base = payload.attached.chunk.address;
    payload.attached.base.offset = base_offset;
    result = osprey_intern_var(ctx, OSPREY_PRED_FIELD_OF, &payload);
    CHECK(result.id != UINT32_MAX, "field variable inserted");
    return result.id;
}

static uint32_t edge_for_local_rule(const OspreyContext *ctx,
                                    const OspreyBpGraph *graph,
                                    uint32_t local_var, uint16_t rule)
{
    if (ctx == NULL || graph == NULL || ctx->graph == NULL ||
        graph->edges == NULL || graph->factors == NULL) return UINT32_MAX;
    for (guint edge_id = 0; edge_id < graph->edges->len; edge_id++) {
        const OspreyBpEdge *edge = &g_array_index(graph->edges,
                                                  OspreyBpEdge, edge_id);
        if (edge->local_var != local_var ||
            edge->local_factor >= graph->factors->len) continue;
        const OspreyBpFactorRef *factor_ref = &g_array_index(
            graph->factors, OspreyBpFactorRef, edge->local_factor);
        const OspreyFactor *factor = g_array_index(
            ctx->graph->factors, OspreyFactor *, factor_ref->graph_factor_id);
        if (factor != NULL && factor->rule == rule) return edge_id;
    }
    return UINT32_MAX;
}

static void test_bp_configuration(void)
{
    const char *name = "BINRADAR_OSPREY_MAX_BP_TABLE_MB";
    char *saved = g_strdup(g_getenv(name));
    OspreyConfig config;

    g_unsetenv(name);
    CHECK(osprey_config_from_env(&config) &&
              config.max_bp_table_bytes == 256u * 1024u * 1024u,
          "BP workspace configuration uses the default budget");
    g_setenv(name, "1", TRUE);
    CHECK(osprey_config_from_env(&config) &&
          config.max_bp_table_bytes == 1024u * 1024u,
          "BP workspace configuration parses exact MiB");
    g_setenv(name, "1MiB", TRUE);
    CHECK(!osprey_config_from_env(&config),
          "BP workspace configuration rejects suffixes");
    g_setenv(name, "0", TRUE);
    CHECK(!osprey_config_from_env(&config),
          "BP workspace configuration rejects zero");
    g_setenv(name, "1 ", TRUE);
    CHECK(!osprey_config_from_env(&config),
          "BP workspace configuration rejects trailing data");
    g_setenv(name, "+1", TRUE);
    CHECK(!osprey_config_from_env(&config),
          "BP workspace configuration rejects non-decimal prefixes");
    g_setenv(name, "18446744073709551616", TRUE);
    CHECK(!osprey_config_from_env(&config),
          "BP workspace configuration rejects integer overflow");
    g_setenv(name, "4097", TRUE);
    CHECK(!osprey_config_from_env(&config),
          "BP workspace configuration rejects values above the bound");
    if (saved != NULL) {
        g_setenv(name, saved, TRUE);
    } else {
        g_unsetenv(name);
    }
    g_free(saved);
}

static void test_basic_projection(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0);
    uint32_t a = add_primitive(ctx, region, 0);
    uint32_t b = add_primitive(ctx, region, 8);
    uint32_t c = add_primitive(ctx, region, 16);
    uint32_t ids[1] = { a };
    OspreyBpGraph *graph = NULL;

    set_seed(ctx, a, 0.0);
    set_seed(ctx, b, 1.0);
    add_prior(ctx, a, 0.0);
    add_prior(ctx, b, 1.0);
    add_secondary(ctx, OSPREY_RULE_CB02, ids, 1, c);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "basic complete projection builds");
    CHECK(graph != NULL && osprey_bp_graph_validate(ctx, graph),
          "basic projection validates in both directions");
    CHECK(graph != NULL && stage5_bp_reference_matches(ctx, graph),
          "basic projection matches independent ownership oracle");
    if (graph != NULL) {
        uint32_t local_a = local_for_offset(ctx, graph, 0);
        uint32_t local_b = local_for_offset(ctx, graph, 8);
        uint32_t local_c = local_for_offset(ctx, graph, 16);
        CHECK(local_a != UINT32_MAX && local_b != UINT32_MAX &&
                  local_c != UINT32_MAX,
              "all basic variables have canonical local IDs");
        CHECK(graph->components->len == 2,
              "secondary bridge creates the expected complete components");
        for (guint i = 0; i < graph->edges->len; i++) {
            const OspreyBpEdge *edge = &g_array_index(graph->edges,
                                                      OspreyBpEdge, i);
            const OspreyBpVarRef *ref = &g_array_index(
                graph->vars, OspreyBpVarRef, edge->local_var);
            const double *message = &graph->msg_vf_current[(size_t)i * 2u];
            if (edge->local_var == local_a) {
                CHECK(ref->base_seed_valid && message[0] == 0.0 &&
                          message[1] == -INFINITY,
                      "exact zero seed is not epsilon-clamped");
            } else if (edge->local_var == local_b) {
                CHECK(ref->base_seed_valid && message[0] == -INFINITY &&
                          message[1] == 0.0,
                      "exact one seed is not epsilon-clamped");
            } else if (edge->local_var == local_c) {
                CHECK(!ref->base_seed_valid &&
                          message[0] == -log(2.0) &&
                          message[1] == -log(2.0),
                      "secondary-only variable starts uniformly");
            }
        }
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_arity_and_components(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x10);
    uint32_t ids[8];
    uint32_t three[2];
    uint32_t four[3];
    OspreyBpGraph *graph = NULL;

    for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) {
        ids[i] = add_primitive(ctx, region, (int64_t)i * 8);
        add_prior(ctx, ids[i], 0.5);
    }
    three[0] = ids[0];
    three[1] = ids[1];
    four[0] = ids[3];
    four[1] = ids[4];
    four[2] = ids[5];
    add_secondary(ctx, OSPREY_RULE_CB02, three, 2, ids[2]);
    add_secondary(ctx, OSPREY_RULE_CB03, four, 3, ids[6]);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK &&
              osprey_bp_graph_validate(ctx, graph) &&
              stage5_bp_reference_matches(ctx, graph),
          "arity-three/four projection matches the independent oracle");
    CHECK(graph != NULL && graph->components->len == 3,
          "disconnected complete graph components are retained");
    if (graph != NULL) {
        bool saw_three = false, saw_four = false;
        for (guint i = 0; i < graph->factors->len; i++) {
            const OspreyBpFactorRef *ref = &g_array_index(
                graph->factors, OspreyBpFactorRef, i);
            if (ref->factor_edge_count == 3) saw_three = true;
            if (ref->factor_edge_count == 4) saw_four = true;
        }
        CHECK(saw_three && saw_four,
              "factor CSR preserves arity-three and arity-four roles");
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_cross_region_bridge(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId global = make_region(OSPREY_REGION_GLOBAL, 0);
    OspreyRegionId stack = make_region(OSPREY_REGION_STACK_FUNCTION, 0x100);
    uint32_t left = add_primitive(ctx, global, 0);
    uint32_t right = add_primitive(ctx, stack, -8);
    uint32_t antecedent = left;
    OspreyBpGraph *graph = NULL;

    add_prior(ctx, left, 0.25);
    add_prior(ctx, right, 0.75);
    add_secondary(ctx, OSPREY_RULE_CD01, &antecedent, 1, right);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK &&
              osprey_bp_graph_validate(ctx, graph) &&
              stage5_bp_reference_matches(ctx, graph),
          "cross-region secondary bridge builds canonically");
    CHECK(graph != NULL && graph->components->len == 1,
          "cross-region bridge is one BP component");
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_exact_seed_values(void)
{
    const double probabilities[] = {
        0.0, 1.0, DBL_MIN, 0.5, nextafter(1.0, 0.0)
    };
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x20);
    OspreyBpGraph *graph = NULL;

    for (unsigned i = 0; i < G_N_ELEMENTS(probabilities); i++) {
        uint32_t id = add_primitive(ctx, region, (int64_t)i * 8);
        set_seed(ctx, id, probabilities[i]);
        add_prior(ctx, id, probabilities[i]);
    }
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK &&
              osprey_bp_graph_validate(ctx, graph),
          "all exact seed values build without clamping");
    if (graph != NULL) {
        for (unsigned i = 0; i < G_N_ELEMENTS(probabilities); i++) {
            uint32_t local = local_for_offset(ctx, graph, (int64_t)i * 8);
            CHECK(local != UINT32_MAX,
                  "exact seed has a canonical local variable");
            if (local == UINT32_MAX) continue;
            const OspreyBpVarRef *ref = &g_array_index(
                graph->vars, OspreyBpVarRef, local);
            CHECK(ref->base_seed_valid &&
                      ref->base_seed[1] == probabilities[i],
                  "base seed retains exact probability payload");
            for (guint edge_id = 0; edge_id < graph->edges->len; edge_id++) {
                const OspreyBpEdge *edge = &g_array_index(
                    graph->edges, OspreyBpEdge, edge_id);
                if (edge->local_var != local) continue;
                double expected_zero = probabilities[i] == 1.0
                    ? 0.0 : 1.0 - probabilities[i];
                double expected_one = probabilities[i];
                double expected_log_zero = expected_zero == 0.0
                    ? -INFINITY : log(expected_zero);
                double expected_log_one = expected_one == 0.0
                    ? -INFINITY : log(expected_one);
                const double *message = &graph->msg_vf_current[
                    (size_t)edge_id * 2u];
                CHECK(message[0] == expected_log_zero &&
                          message[1] == expected_log_one,
                      "seed message uses exact log-domain endpoints");
            }
        }
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_secondary_uniform_seed(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x30);
    uint32_t first = add_primitive(ctx, region, 0);
    uint32_t second = add_primitive(ctx, region, 8);
    OspreyBpGraph *graph = NULL;

    add_secondary(ctx, OSPREY_RULE_CB02, &first, 1, second);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK &&
              osprey_bp_graph_validate(ctx, graph),
          "secondary-only graph builds");
    if (graph != NULL) {
        for (guint i = 0; i < graph->vars->len; i++) {
            const OspreyBpVarRef *ref = &g_array_index(graph->vars,
                                                       OspreyBpVarRef, i);
            CHECK(!ref->base_seed_valid,
                  "secondary-only variable has invalid base seed");
        }
        for (guint i = 0; i < graph->edges->len; i++) {
            CHECK(graph->msg_vf_current[(size_t)i * 2u] == -log(2.0) &&
                      graph->msg_vf_current[(size_t)i * 2u + 1u] == -log(2.0),
                  "secondary-only messages are normalized uniform seeds");
        }
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_round_unary_boundaries(void)
{
    const double probabilities[] = {
        0.0, 1.0, 0.5, DBL_MIN, nextafter(1.0, 0.0)
    };

    for (unsigned i = 0; i < G_N_ELEMENTS(probabilities); i++) {
        OspreyContext *ctx = new_context();
        OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x110 + i);
        uint32_t id = add_primitive(ctx, region, 0);
        OspreyBpGraph *graph = NULL;
        double expected[2];

        add_prior(ctx, id, probabilities[i]);
        CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
              "unary probability graph builds");
        if (graph != NULL) {
            CHECK(compare_round_with_reference(ctx, graph, OSPREY_OK),
                  "unary probability round matches reference");
            set_log_probability_pair(expected, probabilities[i]);
            CHECK(message_pair_close(&graph->msg_fv_next[0], expected),
                  "unary factor message preserves exact probability support");
            CHECK(graph->msg_vf_next[0] == -log(2.0) &&
                      graph->msg_vf_next[1] == -log(2.0),
                  "unary variable message uses the neutral product");
        }
        osprey_bp_graph_free(graph);
        osprey_free(ctx);
    }
}

static void test_round_implication_roles(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x120);
    uint32_t a = add_primitive(ctx, region, 0);
    uint32_t b = add_primitive(ctx, region, 8);
    uint32_t c = add_primitive(ctx, region, 16);
    uint32_t antecedent;
    OspreyBpGraph *graph = NULL;

    add_prior(ctx, a, 0.25);
    add_prior(ctx, b, 0.75);
    add_prior(ctx, c, 0.5);
    antecedent = a;
    add_implication_probability(ctx, OSPREY_RULE_CB02,
                                OSPREY_GRAPH_SECONDARY, false, 0.8,
                                &antecedent, 1, b);
    antecedent = b;
    add_implication_probability(ctx, OSPREY_RULE_CB03,
                                OSPREY_GRAPH_SECONDARY, true, 0.2,
                                &antecedent, 1, c);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "positive and negative implication graph builds");
    if (graph != NULL) {
        CHECK(compare_round_with_reference(ctx, graph, OSPREY_OK),
              "positive and negative implications match reference");
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);

    ctx = new_context();
    region = make_region(OSPREY_REGION_GLOBAL, 0x121);
    uint32_t scalar = add_scalar(ctx, region, 0);
    uint32_t field = add_field(ctx, region, 8, 0);
    graph = NULL;
    antecedent = scalar;
    add_implication_probability(ctx, OSPREY_RULE_CA08,
                                OSPREY_GRAPH_BASE_CA, true, 0.2,
                                &antecedent, 1, field);
    antecedent = field;
    add_implication_probability(ctx, OSPREY_RULE_CA08,
                                OSPREY_GRAPH_BASE_CA, true, 0.2,
                                &antecedent, 1, scalar);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "CA08 bidirectional-role graph builds");
    if (graph != NULL) {
        CHECK(compare_round_with_reference(ctx, graph, OSPREY_OK),
              "CA08 reverse roles match reference");
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_round_arity_three_four(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x130);
    uint32_t ids[4];
    uint32_t three[2];
    uint32_t four[3];
    OspreyBpGraph *graph = NULL;

    for (unsigned i = 0; i < G_N_ELEMENTS(ids); i++) {
        ids[i] = add_primitive(ctx, region, (int64_t)i * 8);
        add_prior(ctx, ids[i], 0.15 + i * 0.2);
    }
    three[0] = ids[0];
    three[1] = ids[1];
    four[0] = ids[0];
    four[1] = ids[1];
    four[2] = ids[2];
    add_implication_probability(ctx, OSPREY_RULE_CB02,
                                OSPREY_GRAPH_SECONDARY, false, 0.8,
                                three, 2, ids[2]);
    add_implication_probability(ctx, OSPREY_RULE_CC07,
                                OSPREY_GRAPH_SECONDARY, false, 0.2,
                                four, 3, ids[3]);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "arity-three/four round graph builds");
    if (graph != NULL) {
        CHECK(compare_round_with_reference(ctx, graph, OSPREY_OK),
              "arity-three/four rounds match reference for every role");
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_round_hard_false(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x140);
    uint32_t id = add_primitive(ctx, region, 0);
    OspreyBpGraph *graph = NULL;
    OspreyFactorResult result = osprey_factor_add_hard_false(
        ctx, OSPREY_RULE_CB06, OSPREY_GRAPH_SECONDARY, id);

    CHECK(result.status == OSPREY_OK, "hard-false factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "hard-false graph builds");
    if (graph != NULL) {
        double expected[2] = { 0.0, -INFINITY };
        CHECK(compare_round_with_reference(ctx, graph, OSPREY_OK),
              "hard-false round matches reference");
        CHECK(message_pair_close(&graph->msg_fv_next[0], expected),
              "hard-false factor preserves exact zero state");
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_round_recipient_exclusion(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x150);
    uint32_t a = add_primitive(ctx, region, 0);
    uint32_t b = add_primitive(ctx, region, 8);
    uint32_t antecedent = a;
    OspreyBpGraph *graph = NULL;

    add_prior(ctx, a, 0.5);
    add_prior(ctx, b, 0.5);
    add_implication_probability(ctx, OSPREY_RULE_CB02,
                                OSPREY_GRAPH_SECONDARY, false, 0.8,
                                &antecedent, 1, b);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "recipient-exclusion graph builds");
    if (graph != NULL) {
        uint32_t local_a = local_for_offset(ctx, graph, 0);
        uint32_t prior_edge = edge_for_local_rule(
            ctx, graph, local_a, OSPREY_RULE_CA01);
        uint32_t implication_edge = edge_for_local_rule(
            ctx, graph, local_a, OSPREY_RULE_CB02);
        double expected_uniform[2] = { -log(2.0), -log(2.0) };
        double expected_extreme[2];
        double expected_factor[2] = { log(0.8 / 1.3), log(0.5 / 1.3) };

        CHECK(local_a != UINT32_MAX && prior_edge != UINT32_MAX &&
                  implication_edge != UINT32_MAX,
              "recipient-exclusion edges resolve");
        if (prior_edge != UINT32_MAX && implication_edge != UINT32_MAX) {
            set_log_probability_pair(
                &graph->msg_fv_current[(size_t)prior_edge * 2u], 0.99);
            set_log_probability_pair(expected_extreme, 0.99);
            CHECK(compare_round_with_reference(ctx, graph, OSPREY_OK),
                  "recipient-exclusion round matches reference");
            CHECK(message_pair_close(
                      &graph->msg_vf_next[(size_t)prior_edge * 2u],
                      expected_uniform),
                  "variable update excludes its recipient factor message");
            CHECK(message_pair_close(
                      &graph->msg_vf_next[(size_t)implication_edge * 2u],
                      expected_extreme),
                  "other variable message receives the extreme incoming state");
            CHECK(message_pair_close(
                      &graph->msg_fv_next[(size_t)implication_edge * 2u],
                      expected_factor),
                  "factor update excludes the recipient variable message");
        }
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_round_failure_paths(void)
{
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x160);
    OspreyContext *ctx = new_context();
    uint32_t id = add_primitive(ctx, region, 0);
    OspreyBpGraph *graph = NULL;
    OspreyBpMessages messages;

    add_prior(ctx, id, 0.5);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "invalid-input graph builds");
    if (graph != NULL) {
        messages = graph_messages(graph);
        graph->msg_fv_current[0] = NAN;
        CHECK(osprey_bp_compute_round(ctx, graph, &messages, NULL) ==
                  OSPREY_INVALID_GRAPH,
              "NaN current message rejects before the round");
        CHECK(isnan(graph->msg_vf_next[0]) && isnan(graph->msg_fv_next[0]),
              "NaN rejection leaves next buffers unusable");
        graph->msg_fv_current[0] = INFINITY;
        CHECK(osprey_bp_compute_round(ctx, graph, &messages, NULL) ==
                  OSPREY_INVALID_GRAPH,
              "positive-infinite current message rejects");
        CHECK(isnan(graph->msg_vf_next[0]) && isnan(graph->msg_fv_next[0]),
              "infinite rejection leaves next buffers unusable");
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);

    ctx = new_context();
    id = add_primitive(ctx, region, 0);
    add_prior(ctx, id, 0.5);
    graph = NULL;
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "malformed-adjacency graph builds");
    if (graph != NULL) {
        messages = graph_messages(graph);
        g_array_index(graph->var_edges, uint32_t, 0) = graph->edges->len;
        CHECK(osprey_bp_compute_round(ctx, graph, &messages, NULL) ==
                  OSPREY_INVALID_GRAPH,
              "out-of-range variable adjacency rejects before access");
        CHECK(isnan(graph->msg_vf_next[0]) && isnan(graph->msg_fv_next[0]),
              "malformed adjacency leaves next buffers unusable");
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);

    ctx = new_context();
    region = make_region(OSPREY_REGION_GLOBAL, 0x161);
    uint32_t a = add_primitive(ctx, region, 0);
    uint32_t b = add_primitive(ctx, region, 8);
    uint32_t antecedent = a;
    add_prior(ctx, a, 0.5);
    OspreyFactorResult hard = osprey_factor_add_hard_false(
        ctx, OSPREY_RULE_CB06, OSPREY_GRAPH_SECONDARY, a);
    CHECK(hard.status == OSPREY_OK, "contradictory hard-false factor inserted");
    add_implication_probability(ctx, OSPREY_RULE_CB02,
                                OSPREY_GRAPH_SECONDARY, false, 0.8,
                                &antecedent, 1, b);
    graph = NULL;
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "impossible-support graph builds");
    if (graph != NULL) {
        uint32_t local_a = local_for_offset(ctx, graph, 0);
        uint32_t prior_edge = edge_for_local_rule(
            ctx, graph, local_a, OSPREY_RULE_CA01);
        uint32_t hard_edge = edge_for_local_rule(
            ctx, graph, local_a, OSPREY_RULE_CB06);
        uint32_t implication_edge = edge_for_local_rule(
            ctx, graph, local_a, OSPREY_RULE_CB02);
        CHECK(prior_edge != UINT32_MAX && hard_edge != UINT32_MAX &&
                  implication_edge != UINT32_MAX,
              "impossible-support edges resolve");
        if (prior_edge != UINT32_MAX && hard_edge != UINT32_MAX &&
            implication_edge != UINT32_MAX) {
            set_log_probability_pair(
                &graph->msg_fv_current[(size_t)prior_edge * 2u], 1.0);
            set_log_probability_pair(
                &graph->msg_fv_current[(size_t)hard_edge * 2u], 0.0);
            CHECK(compare_round_with_reference(ctx, graph,
                                               OSPREY_INVALID_MODEL),
                  "impossible support rejects without a uniform fallback");
        }
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_round_validation_boundaries(void)
{
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x162);
    OspreyContext *ctx = new_context();
    uint32_t id = add_primitive(ctx, region, 0);
    OspreyBpGraph *graph = NULL;
    OspreyBpMessages messages;

    add_prior(ctx, id, 0.2);
    add_prior(ctx, id, 0.3);
    add_prior(ctx, id, 0.4);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "finite-underflow graph builds");
    if (graph != NULL) {
        messages = graph_messages(graph);
        for (guint edge_id = 0; edge_id < graph->edges->len; edge_id++) {
            graph->msg_fv_current[(size_t)edge_id * 2u] = -DBL_MAX;
            graph->msg_fv_current[(size_t)edge_id * 2u + 1u] = 0.0;
        }
        CHECK(osprey_bp_compute_round(ctx, graph, &messages, NULL) ==
                  OSPREY_INVALID_GRAPH,
              "finite message-product underflow rejects");
        for (uint64_t i = 0; i < graph->message_values; i++) {
            CHECK(isnan(graph->msg_vf_next[(size_t)i]) &&
                      isnan(graph->msg_fv_next[(size_t)i]),
                  "underflow rejection poisons both next buffers");
        }
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);

    ctx = new_context();
    region = make_region(OSPREY_REGION_GLOBAL, 0x163);
    uint32_t first = add_primitive(ctx, region, 0);
    uint32_t second = add_primitive(ctx, region, 8);
    uint32_t antecedent = first;
    add_prior(ctx, first, 0.5);
    add_prior(ctx, second, 0.5);
    add_secondary(ctx, OSPREY_RULE_CB02, &antecedent, 1, second);
    graph = NULL;
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "CSR-gap graph builds");
    if (graph != NULL) {
        bool corrupted = false;
        messages = graph_messages(graph);
        for (guint local = 0; local < graph->vars->len; local++) {
            OspreyBpVarRef *ref = &g_array_index(
                graph->vars, OspreyBpVarRef, local);
            if (ref->var_edge_count > 1) {
                ref->var_edge_count--;
                corrupted = true;
                break;
            }
        }
        CHECK(corrupted, "CSR-gap fixture removes one owned edge");
        CHECK(corrupted &&
                  osprey_bp_compute_round(ctx, graph, &messages, NULL) ==
                      OSPREY_INVALID_GRAPH,
              "unowned variable-CSR slot rejects before update");
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);

    ctx = new_context();
    region = make_region(OSPREY_REGION_GLOBAL, 0x164);
    id = add_primitive(ctx, region, 0);
    set_seed(ctx, id, 0.25);
    add_prior(ctx, id, 0.25);
    graph = NULL;
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "overlapping-buffer graph builds");
    if (graph != NULL) {
        size_t values = (size_t)graph->message_values;
        double *overlap = g_new(double, values + 1u);
        double *before = g_new(double, values + 1u);
        memcpy(overlap, graph->msg_vf_current, values * sizeof(double));
        overlap[values] = 1.0;
        memcpy(before, overlap, (values + 1u) * sizeof(double));
        messages = graph_messages(graph);
        messages.vf_current = overlap;
        messages.vf_next = overlap + 1;
        CHECK(osprey_bp_compute_round(ctx, graph, &messages, NULL) ==
                  OSPREY_INVALID_GRAPH,
              "partially overlapping message buffers reject");
        CHECK(memcmp(overlap, before, (values + 1u) * sizeof(double)) == 0,
              "overlap rejection does not mutate current messages");
        g_free(before);
        g_free(overlap);
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static OspreyContext *permutation_context(bool reverse)
{
    OspreyConfig config = bp_config();
    OspreyContext *ctx = new_context_with_config(&config);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x40);
    uint32_t ids[4];
    uint32_t order[4] = { 0, 1, 2, 3 };

    if (reverse) {
        for (unsigned i = 0; i < 4; i++) order[i] = 3 - i;
    }
    for (unsigned i = 0; i < 4; i++) {
        ids[order[i]] = add_primitive(ctx, region, (int64_t)order[i] * 8);
    }
    for (unsigned i = 0; i < 4; i++) set_seed(ctx, ids[i], 0.2 + i * 0.1);
    if (!reverse) {
        for (unsigned i = 0; i < 4; i++) add_prior(ctx, ids[i], 0.2 + i * 0.1);
        uint32_t first[2] = { ids[0], ids[1] };
        uint32_t second[3] = { ids[0], ids[1], ids[2] };
        add_secondary(ctx, OSPREY_RULE_CB02, first, 2, ids[2]);
        add_secondary(ctx, OSPREY_RULE_CB03, second, 3, ids[3]);
    } else {
        uint32_t first[2] = { ids[0], ids[1] };
        uint32_t second[3] = { ids[0], ids[1], ids[2] };
        add_secondary(ctx, OSPREY_RULE_CB03, second, 3, ids[3]);
        add_secondary(ctx, OSPREY_RULE_CB02, first, 2, ids[2]);
        for (int i = 3; i >= 0; i--) {
            add_prior(ctx, ids[i], 0.2 + i * 0.1);
        }
    }
    return ctx;
}

static void test_permutation_dump(void)
{
    OspreyContext *left = permutation_context(false);
    OspreyContext *right = permutation_context(true);
    OspreyBpGraph *left_graph = NULL;
    OspreyBpGraph *right_graph = NULL;
    char *left_dump = NULL;
    char *right_dump = NULL;

    CHECK(osprey_bp_graph_build(left, &left_graph) == OSPREY_OK &&
              osprey_bp_graph_build(right, &right_graph) == OSPREY_OK,
          "permuted graphs build");
    if (left_graph != NULL && right_graph != NULL) {
        left_dump = dump_graph(left, left_graph);
        right_dump = dump_graph(right, right_graph);
        CHECK(left_dump != NULL && right_dump != NULL &&
                  strcmp(left_dump, right_dump) == 0,
              "canonical projection and seed dumps ignore insertion IDs");
        CHECK(compare_round_with_reference(left, left_graph, OSPREY_OK) &&
                  compare_round_with_reference(right, right_graph, OSPREY_OK),
              "permuted one-round messages match the independent reference");
        if (left_graph->edges->len == right_graph->edges->len) {
            for (guint edge_id = 0; edge_id < left_graph->edges->len;
                 edge_id++) {
                size_t index = (size_t)edge_id * 2u;
                CHECK(message_pair_close(
                          &left_graph->msg_vf_next[index],
                          &right_graph->msg_vf_next[index]) &&
                          message_pair_close(
                              &left_graph->msg_fv_next[index],
                              &right_graph->msg_fv_next[index]),
                      "permuted one-round messages are canonical");
            }
        }
    }
    free(left_dump);
    free(right_dump);
    osprey_bp_graph_free(left_graph);
    osprey_bp_graph_free(right_graph);
    osprey_free(left);
    osprey_free(right);
}

static void expect_invalid(OspreyContext *ctx, const char *message)
{
    OspreyBpGraph *graph = NULL;
    OspreyStatus status = osprey_bp_graph_build(ctx, &graph);
    CHECK(status == OSPREY_INVALID_GRAPH && graph == NULL, message);
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_malformed_inputs(void)
{
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x50);
    OspreyContext *ctx;
    OspreyFactor *factor;
    uint32_t ids[2];

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    g_array_index(ctx->graph->vars, OspreyVar, ids[0]).id = 99;
    expect_invalid(ctx, "mismatched variable ID rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    OspreyVar duplicate = g_array_index(ctx->graph->vars, OspreyVar, ids[0]);
    duplicate.id = 1;
    g_array_append_val(ctx->graph->vars, duplicate);
    add_prior(ctx, ids[0], 0.5);
    expect_invalid(ctx, "duplicate semantic variable rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    OspreyFactor *original = g_array_index(ctx->graph->factors,
                                           OspreyFactor *, 0);
    OspreyFactor *duplicate_factor = g_new(OspreyFactor, 1);
    *duplicate_factor = *original;
    duplicate_factor->id = 1;
    duplicate_factor->var_ids = g_new(uint32_t, original->num_vars);
    memcpy(duplicate_factor->var_ids, original->var_ids,
           (size_t)original->num_vars * sizeof(uint32_t));
    g_array_append_val(ctx->graph->factors, duplicate_factor);
    expect_invalid(ctx, "duplicate semantic factor rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 0);
    factor->id = 99;
    expect_invalid(ctx, "mismatched factor ID rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 0);
    factor->num_vars = OSPREY_FACTOR_MAX_ARITY + 1;
    expect_invalid(ctx, "factor arity above the bound rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 0);
    factor->p = INFINITY;
    expect_invalid(ctx, "positive-infinite factor probability rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    ids[1] = add_primitive(ctx, region, 8);
    add_prior(ctx, ids[0], 0.5);
    add_prior(ctx, ids[1], 0.5);
    uint32_t antecedent = ids[0];
    add_secondary(ctx, OSPREY_RULE_CB02, &antecedent, 1, ids[1]);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 2);
    factor->var_ids[1] = factor->var_ids[0];
    expect_invalid(ctx, "repeated factor role rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 0);
    factor->stage = OSPREY_GRAPH_SECONDARY;
    expect_invalid(ctx, "bad stage and rule pairing rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    add_prior(ctx, ids[0], 0.5);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 0);
    factor->p = NAN;
    expect_invalid(ctx, "non-finite factor probability rejects");

    ctx = new_context();
    ids[0] = add_primitive(ctx, region, 0);
    ids[1] = add_primitive(ctx, region, 8);
    add_prior(ctx, ids[0], 0.5);
    add_prior(ctx, ids[1], 0.5);
    antecedent = ids[0];
    add_secondary(ctx, OSPREY_RULE_CB02, &antecedent, 1, ids[1]);
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 2);
    factor->head_idx = 2;
    expect_invalid(ctx, "bad factor head rejects");

    ctx = new_context();
    add_primitive(ctx, region, 0);
    expect_invalid(ctx, "factorless variable rejects");
}

static void test_reverse_adjacency_validation(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x60);
    uint32_t first = add_primitive(ctx, region, 0);
    uint32_t second = add_primitive(ctx, region, 8);
    uint32_t antecedent = first;
    OspreyBpGraph *graph = NULL;

    add_prior(ctx, first, 0.5);
    add_prior(ctx, second, 0.5);
    add_secondary(ctx, OSPREY_RULE_CB02, &antecedent, 1, second);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK,
          "reverse-adjacency fixture builds");
    if (graph != NULL && graph->var_edges->len > 1) {
        uint32_t saved = g_array_index(graph->var_edges, uint32_t, 0);
        g_array_index(graph->var_edges, uint32_t, 0) =
            g_array_index(graph->var_edges, uint32_t, 1);
        CHECK(!osprey_bp_graph_validate(ctx, graph),
              "overwritten variable adjacency is rejected");
        g_array_index(graph->var_edges, uint32_t, 0) = saved;
        OspreyBpEdge *edge = &g_array_index(graph->edges, OspreyBpEdge, 0);
        uint32_t saved_position = edge->key.factor_position;
        edge->key.factor_position = saved_position + 1;
        CHECK(!osprey_bp_graph_validate(ctx, graph),
              "corrupted semantic edge role is rejected");
        edge->key.factor_position = saved_position;
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_component_maximality_validation(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x70);
    uint32_t first_id = add_primitive(ctx, region, 0);
    uint32_t second_id = add_primitive(ctx, region, 8);
    OspreyBpGraph *graph = NULL;

    add_prior(ctx, first_id, 0.5);
    add_prior(ctx, second_id, 0.5);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK &&
              graph != NULL && graph->components->len == 2,
          "disconnected-component validation fixture builds");
    if (graph != NULL && graph->components->len == 2) {
        OspreyBpComponent *first = g_ptr_array_index(graph->components, 0);
        OspreyBpComponent *second = g_ptr_array_index(graph->components, 1);
        uint64_t removed_bytes = sizeof(*second) + 3u * sizeof(GArray) +
                                 sizeof(gpointer);

        g_array_append_vals(first->local_vars, second->local_vars->data,
                            second->local_vars->len);
        g_array_append_vals(first->local_factors, second->local_factors->data,
                            second->local_factors->len);
        g_array_append_vals(first->edges, second->edges->data,
                            second->edges->len);
        g_ptr_array_remove_index(graph->components, 1);
        g_array_free(second->local_vars, TRUE);
        g_array_free(second->local_factors, TRUE);
        g_array_free(second->edges, TRUE);
        g_free(second);
        graph->workspace_bytes -= removed_bytes;

        CHECK(!osprey_bp_graph_validate(ctx, graph),
              "validator rejects one component containing disconnected subgraphs");
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static OspreyStatus build_basic_with_limit(uint64_t limit,
                                           OspreyBpGraph **out)
{
    OspreyConfig config = bp_config();
    OspreyContext *ctx;
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x80);
    uint32_t ids[3];
    OspreyStatus status;

    config.max_bp_table_bytes = limit;
    ctx = new_context_with_config(&config);
    ids[0] = add_primitive(ctx, region, 0);
    ids[1] = add_primitive(ctx, region, 8);
    ids[2] = add_primitive(ctx, region, 16);
    add_prior(ctx, ids[0], 0.25);
    add_prior(ctx, ids[1], 0.5);
    add_prior(ctx, ids[2], 0.75);
    uint32_t antecedents[2] = { ids[0], ids[1] };
    add_secondary(ctx, OSPREY_RULE_CB02, antecedents, 2, ids[2]);
    status = osprey_bp_graph_build(ctx, out);
    if (status != OSPREY_OK) osprey_bp_graph_free(*out);
    osprey_free(ctx);
    return status;
}

static void test_workspace_boundaries(void)
{
    OspreyConfig config = bp_config();
    OspreyContext *probe_ctx = new_context_with_config(&config);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x80);
    uint32_t ids[3];
    OspreyBpGraph *probe = NULL;
    uint64_t required;

    ids[0] = add_primitive(probe_ctx, region, 0);
    ids[1] = add_primitive(probe_ctx, region, 8);
    ids[2] = add_primitive(probe_ctx, region, 16);
    add_prior(probe_ctx, ids[0], 0.25);
    add_prior(probe_ctx, ids[1], 0.5);
    add_prior(probe_ctx, ids[2], 0.75);
    uint32_t antecedents[2] = { ids[0], ids[1] };
    add_secondary(probe_ctx, OSPREY_RULE_CB02, antecedents, 2, ids[2]);
    CHECK(osprey_bp_graph_build(probe_ctx, &probe) == OSPREY_OK &&
              probe != NULL && osprey_bp_graph_validate(probe_ctx, probe),
          "workspace probe builds");
    required = probe == NULL ? 0 : probe->workspace_bytes;
    osprey_bp_graph_free(probe);
    osprey_free(probe_ctx);
    if (required != 0) {
        OspreyBpGraph *at_bound = NULL;
        OspreyBpGraph *below_bound = NULL;
        CHECK(build_basic_with_limit(required, &at_bound) == OSPREY_OK &&
                  at_bound != NULL,
              "workspace succeeds exactly at its checked bound");
        CHECK(build_basic_with_limit(required - 1, &below_bound) ==
                  OSPREY_LIMIT_EXCEEDED && below_bound == NULL,
              "workspace rejects one byte below its checked bound");
        osprey_bp_graph_free(at_bound);
        osprey_bp_graph_free(below_bound);
    }
}

static void test_allocation_failures(void)
{
    bool saw_success = false;
    int64_t success_at = -1;

    for (int64_t fail_after = 0; fail_after < 256; fail_after++) {
        OspreyContext *ctx = new_context();
        OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x90);
        uint32_t first = add_primitive(ctx, region, 0);
        uint32_t second = add_primitive(ctx, region, 8);
        uint32_t antecedent = first;
        OspreyBpGraph *graph = NULL;
        add_prior(ctx, first, 0.5);
        add_prior(ctx, second, 0.5);
        add_secondary(ctx, OSPREY_RULE_CB02, &antecedent, 1, second);
        osprey_bp_test_set_alloc_fail_after(fail_after);
        OspreyStatus status = osprey_bp_graph_build(ctx, &graph);
        osprey_bp_test_set_alloc_fail_after(-1);
        if (status == OSPREY_OK) {
            saw_success = true;
            success_at = fail_after;
            CHECK(graph != NULL && osprey_bp_graph_validate(ctx, graph),
                  "allocation-failure sweep eventually builds a valid graph");
        } else {
            CHECK(status == OSPREY_INVALID_GRAPH && graph == NULL,
                  "allocation failure rejects without a partial graph");
        }
        osprey_bp_graph_free(graph);
        osprey_free(ctx);
        if (saw_success) break;
    }
    CHECK(saw_success && success_at > 0,
          "every owned BP allocation has a deterministic failure point");
}

static void test_rebuild_after_failure(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0xa0);
    uint32_t id = add_primitive(ctx, region, 0);
    OspreyBpGraph *graph = NULL;

    add_prior(ctx, id, 0.5);
    osprey_bp_test_set_alloc_fail_after(0);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_INVALID_GRAPH &&
              graph == NULL, "first BP allocation failure is isolated");
    osprey_bp_test_set_alloc_fail_after(-1);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL &&
              osprey_bp_graph_validate(ctx, graph),
          "build after failure succeeds");
    osprey_bp_graph_free(graph);
    graph = NULL;
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL &&
              osprey_bp_graph_validate(ctx, graph),
          "repeated build and free remain deterministic");
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static uint32_t next_random(uint32_t *state)
{
    *state = *state * 1664525u + 1013904223u;
    return *state;
}

static double generated_probability(uint32_t value)
{
    switch (value % 7u) {
    case 0: return 0.0;
    case 1: return 1.0;
    case 2: return DBL_MIN;
    case 3: return 0.5;
    case 4: return nextafter(1.0, 0.0);
    case 5: return 0.2;
    default: return 0.8;
    }
}

static OspreyContext *reverse_clone_context(const OspreyContext *source)
{
    OspreyContext *copy;
    uint32_t *remap;

    if (source == NULL || source->graph == NULL || source->graph->vars == NULL ||
        source->graph->factors == NULL || source->graph->vars->len == 0) {
        return NULL;
    }
    copy = new_context_with_config(&source->config);
    if (copy == NULL || copy->graph == NULL) {
        osprey_free(copy);
        return NULL;
    }
    remap = g_try_new(uint32_t, source->graph->vars->len);
    if (remap == NULL) {
        osprey_free(copy);
        return NULL;
    }
    for (guint i = source->graph->vars->len; i > 0; i--) {
        uint32_t graph_id = i - 1u;
        const OspreyVar *original = &g_array_index(
            source->graph->vars, OspreyVar, graph_id);
        OspreyInternResult result = osprey_intern_var(
            copy, original->kind, &original->payload);
        if (result.id == UINT32_MAX) goto fail;
        OspreyVar duplicate = *original;
        duplicate.id = result.id;
        g_array_index(copy->graph->vars, OspreyVar, result.id) = duplicate;
        remap[graph_id] = result.id;
    }
    for (guint i = source->graph->factors->len; i > 0; i--) {
        const OspreyFactor *factor = g_array_index(
            source->graph->factors, OspreyFactor *, i - 1u);
        uint32_t var_ids[OSPREY_FACTOR_MAX_ARITY];
        for (uint32_t position = 0; position < factor->num_vars; position++) {
            if (factor->var_ids[position] >= source->graph->vars->len) {
                goto fail;
            }
            var_ids[position] = remap[factor->var_ids[position]];
        }
        OspreyFactorResult result = osprey_factor_add_ex(
            copy, factor->rule, factor->stage, factor->potential_kind,
            factor->head_idx, factor->negative != 0, factor->p, var_ids,
            factor->num_vars);
        if (result.status != OSPREY_OK) goto fail;
    }
    g_free(remap);
    return copy;

fail:
    g_free(remap);
    osprey_free(copy);
    return NULL;
}

static void dump_generated_round_failure(unsigned sample,
                                         const OspreyContext *ctx,
                                         const OspreyBpGraph *graph)
{
    fprintf(stderr, "generated round state at seed %u\n", sample);
    if (ctx != NULL && ctx->graph != NULL) {
        osprey_graph_dump_file(ctx, stderr);
    }
    if (graph == NULL) return;
    for (guint edge_id = 0; edge_id < graph->edges->len; edge_id++) {
        size_t index = (size_t)edge_id * 2u;
        fprintf(stderr, "CURRENT %u vf %a %a fv %a %a\n", edge_id,
                graph->msg_vf_current[index],
                graph->msg_vf_current[index + 1u],
                graph->msg_fv_current[index],
                graph->msg_fv_current[index + 1u]);
    }
}

static bool brute_force_beliefs(const OspreyContext *ctx,
                                const OspreyBpGraph *graph, double *out)
{
    uint32_t variable_count;
    uint64_t assignment_count;
    long double total = 0.0L;
    long double *true_weights;

    if (ctx == NULL || graph == NULL || out == NULL || ctx->graph == NULL ||
        ctx->graph->vars == NULL || ctx->graph->factors == NULL ||
        ctx->graph->vars->len == 0 || ctx->graph->vars->len >= 63 ||
        graph->local_by_graph_var == NULL) return false;
    variable_count = ctx->graph->vars->len;
    assignment_count = UINT64_C(1) << variable_count;
    true_weights = g_new0(long double, variable_count);
    for (uint64_t mask = 0; mask < assignment_count; mask++) {
        long double log_weight = 0.0L;
        bool supported = true;

        for (guint factor_index = 0;
             factor_index < ctx->graph->factors->len; factor_index++) {
            const OspreyFactor *factor = g_array_index(
                ctx->graph->factors, OspreyFactor *, factor_index);
            uint8_t assignment[OSPREY_FACTOR_MAX_ARITY];
            double factor_log_weight;

            if (factor == NULL || factor->num_vars == 0 ||
                factor->num_vars > OSPREY_FACTOR_MAX_ARITY) {
                g_free(true_weights);
                return false;
            }
            for (uint32_t position = 0; position < factor->num_vars;
                 position++) {
                uint32_t graph_var = factor->var_ids[position];
                if (graph_var >= variable_count) {
                    g_free(true_weights);
                    return false;
                }
                assignment[position] = (uint8_t)((mask >> graph_var) & 1u);
            }
            if (!osprey_factor_log_weight(factor, assignment,
                                           &factor_log_weight)) {
                g_free(true_weights);
                return false;
            }
            if (factor_log_weight == -INFINITY) {
                supported = false;
                break;
            }
            if (!isfinite(factor_log_weight)) {
                g_free(true_weights);
                return false;
            }
            log_weight += (long double)factor_log_weight;
        }
        if (!supported) continue;
        long double weight = expl(log_weight);
        if (!(weight >= 0.0L) || !isfinite((double)weight)) {
            g_free(true_weights);
            return false;
        }
        total += weight;
        for (uint32_t graph_var = 0; graph_var < variable_count;
             graph_var++) {
            if ((mask >> graph_var) & 1u) true_weights[graph_var] += weight;
        }
    }
    if (!(total > 0.0L) || !isfinite((double)total)) {
        g_free(true_weights);
        return false;
    }
    for (uint32_t local = 0; local < variable_count; local++) {
        uint32_t graph_var = graph->vars == NULL || local >= graph->vars->len
            ? UINT32_MAX
            : g_array_index(graph->vars, OspreyBpVarRef, local).graph_var_id;
        if (graph_var >= variable_count) {
            g_free(true_weights);
            return false;
        }
        out[local] = (double)(true_weights[graph_var] / total);
        if (!isfinite(out[local]) || out[local] < 0.0 || out[local] > 1.0) {
            g_free(true_weights);
            return false;
        }
    }
    g_free(true_weights);
    return true;
}

static uint64_t double_bits(double value)
{
    uint64_t bits;
    memcpy(&bits, &value, sizeof(bits));
    return bits;
}

static double generated_forest_probability(uint32_t value)
{
    static const double probabilities[] = {
        0.015, 0.05, 0.12, 0.25, 0.4, 0.6, 0.75, 0.88, 0.95, 0.985
    };
    return probabilities[value % G_N_ELEMENTS(probabilities)];
}

static OspreyContext *generated_forest_context(unsigned sample)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL,
                                        0x200u + sample);
    uint32_t state = 0x6d2b79f5u ^ (sample * 0x9e3779b9u);
    uint32_t ids[12];
    uint32_t order[12];
    uint32_t count;
    uint32_t cursor = 0;
    uint16_t rule = OSPREY_RULE_CB01;

    if (ctx == NULL) return NULL;
    count = 1u + next_random(&state) % 12u;
    for (uint32_t i = 0; i < count; i++) order[i] = i;
    for (uint32_t i = count; i > 1; i--) {
        uint32_t selected = next_random(&state) % i;
        uint32_t swap = order[i - 1u];
        order[i - 1u] = order[selected];
        order[selected] = swap;
    }
    for (uint32_t position = 0; position < count; position++) {
        uint32_t semantic_id = order[position];
        double probability = generated_forest_probability(
            next_random(&state));
        ids[semantic_id] = add_primitive(ctx, region,
                                         (int64_t)semantic_id * 16);
        set_seed(ctx, ids[semantic_id], probability);
        if (!add_prior(ctx, ids[semantic_id], probability)) goto fail;
    }
    while (cursor < count) {
        uint32_t remaining = count - cursor;
        uint32_t group_size = 1u + next_random(&state) %
            (remaining < 5u ? remaining : 5u);
        uint32_t parent = ids[cursor];
        uint32_t group_cursor = cursor + 1u;
        uint32_t group_end = cursor + group_size;

        while (group_cursor < group_end) {
            uint32_t available = group_end - group_cursor;
            uint32_t fanout = 1u;
            uint32_t selector = next_random(&state);
            uint32_t antecedents[3];

            if (available >= 3u && selector % 3u == 0u) {
                fanout = 3u;
            } else if (available >= 2u && selector % 2u == 0u) {
                fanout = 2u;
            }
            antecedents[0] = parent;
            for (uint32_t i = 1; i < fanout; i++) {
                antecedents[i] = ids[group_cursor + i - 1u];
            }
            if (!add_implication_probability(
                    ctx, rule, OSPREY_GRAPH_SECONDARY, false,
                    generated_forest_probability(next_random(&state)),
                    antecedents, fanout, ids[group_cursor + fanout - 1u])) {
                goto fail;
            }
            parent = ids[group_cursor + fanout - 1u];
            group_cursor += fanout;
            rule = (uint16_t)(OSPREY_RULE_CB01 +
                              (rule - OSPREY_RULE_CB01 + 1u) % 9u);
        }
        cursor = group_end;
    }
    return ctx;

fail:
    osprey_free(ctx);
    return NULL;
}

static bool fixed_result_metadata_equal(const OspreyBpResult *left,
                                        const OspreyBpResult *right)
{
    if (left == NULL || right == NULL || left->status != right->status ||
        left->iterations != right->iterations ||
        left->stable_rounds != right->stable_rounds ||
        left->nonconverged_component != right->nonconverged_component ||
        left->best_iteration != right->best_iteration ||
        double_bits(left->final_max_delta) !=
            double_bits(right->final_max_delta) ||
        double_bits(left->best_max_delta) !=
            double_bits(right->best_max_delta) ||
        left->beliefs == NULL || right->beliefs == NULL ||
        left->beliefs->len != right->beliefs->len) return false;
    for (guint i = 0; i < left->beliefs->len; i++) {
        if (double_bits(g_array_index(left->beliefs, double, i)) !=
            double_bits(g_array_index(right->beliefs, double, i))) return false;
    }
    return true;
}

static void dump_fixed_solver_failure(unsigned sample,
                                      const OspreyContext *ctx,
                                      const OspreyBpGraph *graph,
                                      const OspreyBpResult *result)
{
    fprintf(stderr, "fixed forest failure seed %u\n", sample);
    if (ctx != NULL && ctx->graph != NULL) osprey_graph_dump_file(ctx, stderr);
    if (graph != NULL) dump_generated_round_failure(sample, ctx, graph);
    if (result != NULL) {
        fprintf(stderr, "result status %d iters %u stable %u component %u "
                "final %016llx best %016llx best-iteration %u\n",
                result->status, result->iterations, result->stable_rounds,
                result->nonconverged_component,
                (unsigned long long)double_bits(result->final_max_delta),
                (unsigned long long)double_bits(result->best_max_delta),
                result->best_iteration);
    }
}

static void test_fixed_damping(void)
{
    double current[2];
    double raw[2];
    double damped[2];
    double expected[2];
    double geometric_true;

    set_log_probability_pair(current, 0.2);
    set_log_probability_pair(raw, 0.6);
    CHECK(osprey_bp_damp_pair(current, raw, 0.5, damped),
          "probability-space damping accepts normalized pairs");
    set_log_probability_pair(expected, 0.4);
    CHECK(message_pair_close(damped, expected),
          "damping matches the arithmetic probability mixture");
    geometric_true = sqrt(0.2 * 0.6);
    CHECK(fabs(exp(damped[1]) - geometric_true) > 1e-3,
          "damping is not geometric interpolation of log values");
    CHECK(osprey_bp_damp_pair(current, raw, 1.0, damped) &&
              damped[0] == current[0] && damped[1] == current[1],
          "damping coefficient one retains the current message");
    CHECK(osprey_bp_damp_pair(current, raw, 0.0, damped) &&
              damped[0] == raw[0] && damped[1] == raw[1],
          "damping coefficient zero retains the raw message");
    current[0] = 0.0;
    current[1] = -INFINITY;
    raw[0] = -INFINITY;
    raw[1] = 0.0;
    CHECK(osprey_bp_damp_pair(current, raw, 0.5, damped) &&
              message_pair_close(damped,
                                 (double[2]){ -log(2.0), -log(2.0) }),
          "damping mixes complementary hard-zero support without epsilon");
}

static void test_fixed_graph_solver(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x1a0);
    uint32_t ids[3];
    uint32_t antecedent;
    OspreyBpGraph *graph = NULL;
    OspreyBpResult *result = NULL;
    OspreyBpResult *repeat = NULL;
    double expected[3];
    OspreyStatus status;

    ids[0] = add_primitive(ctx, region, 0);
    ids[1] = add_primitive(ctx, region, 8);
    ids[2] = add_primitive(ctx, region, 16);
    add_prior(ctx, ids[0], 0.25);
    add_prior(ctx, ids[1], 0.75);
    add_prior(ctx, ids[2], 0.4);
    antecedent = ids[0];
    add_implication_probability(ctx, OSPREY_RULE_CB01,
                                OSPREY_GRAPH_SECONDARY, false, 0.8,
                                &antecedent, 1, ids[1]);
    antecedent = ids[1];
    add_implication_probability(ctx, OSPREY_RULE_CB02,
                                OSPREY_GRAPH_SECONDARY, false, 0.65,
                                &antecedent, 1, ids[2]);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "fixed-graph solver fixture builds");
    if (graph == NULL) {
        osprey_free(ctx);
        return;
    }
    CHECK(brute_force_beliefs(ctx, graph, expected),
          "independent tree marginal oracle evaluates the fixture");
    status = osprey_bp_solve_fixed(ctx, graph, &result);
    CHECK(status == OSPREY_OK && result != NULL &&
              result->status == OSPREY_OK,
          "fixed graph converges with the real stability policy");
    if (result != NULL) {
        CHECK(result->iterations >= 10u && result->iterations <= 500u &&
                  result->stable_rounds == 10u &&
                  result->best_iteration > 0 &&
                  isfinite(result->best_max_delta),
              "fixed result carries deterministic convergence metadata");
        CHECK(result->beliefs != NULL && result->beliefs->len == 3,
              "fixed result owns canonical beliefs");
        if (result->beliefs != NULL && result->beliefs->len == 3) {
            for (guint local = 0; local < result->beliefs->len; local++) {
                double actual = g_array_index(result->beliefs, double, local);
                CHECK(fabs(actual - expected[local]) <= 2e-8,
                      "tree BP belief matches the policy-bounded oracle");
            }
        }
    }
    CHECK(g_array_index(ctx->graph->vars, OspreyVar, ids[0]).belief == 0.0 &&
              g_array_index(ctx->graph->vars, OspreyVar, ids[1]).belief == 0.0 &&
              g_array_index(ctx->graph->vars, OspreyVar, ids[2]).belief == 0.0 &&
              g_array_index(ctx->graph->vars, OspreyVar, ids[0]).belief_valid == 0,
          "fixed solver does not publish production beliefs");
    CHECK(osprey_bp_graph_validate(ctx, graph),
          "completed fixed graph remains internally valid");
    CHECK(result != NULL && osprey_bp_commit_result(ctx, graph, result) ==
              OSPREY_OK,
          "successful fixed result commits atomically");
    for (guint local = 0; local < graph->vars->len; local++) {
        uint32_t graph_id = g_array_index(graph->vars, OspreyBpVarRef,
                                          local).graph_var_id;
        OspreyVar *variable = &g_array_index(ctx->graph->vars, OspreyVar,
                                             graph_id);
        CHECK(variable->belief_valid == 1 &&
                  variable->belief == g_array_index(result->beliefs, double,
                                                    local),
              "commit publishes every canonical belief exactly once");
    }
    CHECK(osprey_bp_graph_validate(ctx, graph),
          "committed fixed graph validates after source beliefs change");
    if (result != NULL) {
        double committed[3];
        uint8_t committed_valid[3];
        GArray *saved_vars = graph->vars;
        for (guint local = 0; local < graph->vars->len; local++) {
            uint32_t graph_id = g_array_index(graph->vars, OspreyBpVarRef,
                                              local).graph_var_id;
            const OspreyVar *variable = &g_array_index(
                ctx->graph->vars, OspreyVar, graph_id);
            committed[local] = variable->belief;
            committed_valid[local] = variable->belief_valid;
        }
        g_array_index(result->beliefs, double, 0) = NAN;
        CHECK(osprey_bp_commit_result(ctx, graph, result) ==
                  OSPREY_INVALID_GRAPH,
              "invalid temporary belief rejects before publication");
        graph->vars = NULL;
        CHECK(osprey_bp_commit_result(ctx, graph, result) ==
                  OSPREY_INVALID_GRAPH,
              "malformed commit graph rejects without dereference");
        graph->vars = saved_vars;
        for (guint local = 0; local < graph->vars->len; local++) {
            uint32_t graph_id = g_array_index(graph->vars, OspreyBpVarRef,
                                              local).graph_var_id;
            const OspreyVar *variable = &g_array_index(
                ctx->graph->vars, OspreyVar, graph_id);
            CHECK(variable->belief == committed[local] &&
                      variable->belief_valid == committed_valid[local],
                  "commit rejection preserves every published belief");
        }
        g_array_index(result->beliefs, double, 0) = committed[0];
    }
    osprey_bp_result_free(result);
    result = NULL;
    status = osprey_bp_solve_fixed(ctx, graph, &repeat);
    CHECK(status == OSPREY_OK && repeat != NULL,
          "repeated solve accepts the iterated message state");
    if (repeat != NULL) {
        for (guint local = 0; local < repeat->beliefs->len; local++) {
            CHECK(fabs(g_array_index(repeat->beliefs, double, local) -
                       expected[local]) <= 1e-10,
                  "repeated fixed solve retains tree marginals");
        }
    }
    osprey_bp_result_free(repeat);
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_fixed_solver_failures(void)
{
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x1b0);
    OspreyContext *ctx = new_context();
    uint32_t id = add_primitive(ctx, region, 0);
    OspreyBpGraph *graph = NULL;
    OspreyBpResult *result = NULL;
    OspreyStatus status;
    double before = 0.37;

    set_seed(ctx, id, before);
    add_prior(ctx, id, 0.0);
    add_prior(ctx, id, 1.0);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "impossible fixed graph builds");
    if (graph != NULL) {
        CHECK(osprey_bp_solve_fixed(ctx, graph, &result) ==
                  OSPREY_INVALID_MODEL && result != NULL &&
                  result->status == OSPREY_INVALID_MODEL,
              "impossible fixed component rejects as an invalid model");
        CHECK(g_array_index(ctx->graph->vars, OspreyVar, id).belief == before &&
                  g_array_index(ctx->graph->vars, OspreyVar, id).belief_valid == 1,
              "impossible fixed solve leaves source belief unchanged");
        if (result != NULL) {
            bool all_nan = true;
            for (guint i = 0; i < result->beliefs->len; i++) {
                if (!isnan(g_array_index(result->beliefs, double, i))) {
                    all_nan = false;
                }
            }
            CHECK(all_nan, "impossible result publishes no temporary belief");
        }
        CHECK(osprey_bp_graph_validate(ctx, graph),
              "impossible fixed solve restores the initial graph state");
    }
    osprey_bp_result_free(result);
    osprey_bp_graph_free(graph);
    osprey_free(ctx);

    ctx = new_context();
    uint32_t valid_id = add_primitive(ctx, region, 8);
    uint32_t impossible_id = add_primitive(ctx, region, 16);
    double valid_before = 0.73;
    double impossible_before = 0.41;
    set_seed(ctx, valid_id, valid_before);
    set_seed(ctx, impossible_id, impossible_before);
    add_prior(ctx, valid_id, valid_before);
    add_prior(ctx, impossible_id, 0.0);
    add_prior(ctx, impossible_id, 1.0);
    graph = NULL;
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL &&
              graph->components->len == 2,
          "later impossible component graph builds separately");
    if (graph != NULL) {
        char *before_dump = dump_graph(ctx, graph);
        status = osprey_bp_solve_fixed(ctx, graph, &result);
        CHECK(status == OSPREY_INVALID_MODEL && result != NULL &&
                  result->status == OSPREY_INVALID_MODEL,
              "later impossible component rejects the whole solve");
        CHECK(g_array_index(ctx->graph->vars, OspreyVar, valid_id).belief ==
                  valid_before &&
                  g_array_index(ctx->graph->vars, OspreyVar,
                                impossible_id).belief == impossible_before &&
                  g_array_index(ctx->graph->vars, OspreyVar,
                                valid_id).belief_valid == 1 &&
                  g_array_index(ctx->graph->vars, OspreyVar,
                                impossible_id).belief_valid == 1,
              "later impossible component leaves earlier beliefs unchanged");
        osprey_bp_result_free(result);
        result = NULL;
        CHECK(osprey_bp_solve_fixed(ctx, graph, &result) ==
                  OSPREY_INVALID_MODEL && result != NULL &&
                  result->status == OSPREY_INVALID_MODEL,
              "repeated impossible solve remains rejected");
        char *after_dump = dump_graph(ctx, graph);
        CHECK(before_dump != NULL && after_dump != NULL &&
                  strcmp(before_dump, after_dump) == 0,
              "repeated impossible rejection preserves graph state");
        free(before_dump);
        free(after_dump);
    }
    osprey_bp_result_free(result);
    osprey_bp_graph_free(graph);
    osprey_free(ctx);

    ctx = new_context();
    id = add_primitive(ctx, region, 8);
    add_prior(ctx, id, 0.5);
    graph = NULL;
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "allocation-failure fixed graph builds");
    if (graph != NULL) {
        static const char *const allocation_stages[] = {
            "result ownership", "result belief-array ownership",
            "saved variable-message ownership",
            "saved factor-message ownership", "saved-belief ownership"
        };
        for (int64_t fail_after = 0;
             fail_after < (int64_t)G_N_ELEMENTS(allocation_stages);
             fail_after++) {
            char *before_dump = dump_graph(ctx, graph);
            char *after_dump;
            result = NULL;
            osprey_bp_test_set_alloc_fail_after(fail_after);
            OspreyStatus allocation_status = osprey_bp_solve_fixed(
                ctx, graph, &result);
            osprey_bp_test_set_alloc_fail_after(-1);
            after_dump = dump_graph(ctx, graph);
            CHECK(allocation_status == OSPREY_INVALID_GRAPH && result == NULL,
                  allocation_stages[fail_after]);
            CHECK(before_dump != NULL && after_dump != NULL &&
                      strcmp(before_dump, after_dump) == 0,
                  "fixed allocation failure preserves exact graph state");
            free(before_dump);
            free(after_dump);
        }
        CHECK(osprey_bp_graph_validate(ctx, graph),
              "fixed allocation failures preserve graph ownership");
        CHECK(osprey_bp_solve_fixed(ctx, graph, &result) == OSPREY_OK &&
                  result != NULL,
              "fixed solver recovers after every ownership failure");
        osprey_bp_result_free(result);
        result = NULL;
    }
    osprey_bp_graph_free(graph);
    osprey_free(ctx);

    ctx = new_context();
    id = add_primitive(ctx, region, 16);
    add_prior(ctx, id, 0.5);
    graph = NULL;
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "non-finite fixed graph builds");
    if (graph != NULL) {
        graph->msg_fv_current[0] = NAN;
        CHECK(osprey_bp_solve_fixed(ctx, graph, &result) ==
                  OSPREY_INVALID_GRAPH && result == NULL,
              "non-finite current state rejects before publication");
    }
    osprey_bp_result_free(result);
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_fixed_workspace_failure(void)
{
    OspreyConfig config = bp_config();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x1b2);
    OspreyContext *probe = new_context_with_config(&config);
    OspreyContext *ctx = NULL;
    OspreyBpGraph *probe_graph = NULL;
    OspreyBpGraph *graph = NULL;
    OspreyBpResult *result = NULL;
    uint64_t graph_workspace = 0;
    char *before = NULL;
    char *after = NULL;

    uint32_t probe_id = add_primitive(probe, region, 0);
    add_prior(probe, probe_id, 0.5);
    CHECK(osprey_bp_graph_build(probe, &probe_graph) == OSPREY_OK &&
              probe_graph != NULL,
          "fixed workspace probe builds");
    if (probe_graph != NULL) graph_workspace = probe_graph->workspace_bytes;
    osprey_bp_graph_free(probe_graph);
    osprey_free(probe);
    if (graph_workspace == 0) return;

    config.max_bp_table_bytes = graph_workspace;
    ctx = new_context_with_config(&config);
    uint32_t id = add_primitive(ctx, region, 0);
    add_prior(ctx, id, 0.5);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL &&
              osprey_bp_graph_validate(ctx, graph),
          "fixed workspace-limit graph validates at its graph-only bound");
    if (graph != NULL) {
        before = dump_graph(ctx, graph);
        CHECK(osprey_bp_solve_fixed(ctx, graph, &result) ==
                  OSPREY_LIMIT_EXCEEDED && result == NULL,
              "fixed result workspace rejects below its solver bound");
        after = dump_graph(ctx, graph);
        CHECK(before != NULL && after != NULL && strcmp(before, after) == 0,
              "workspace rejection preserves exact fixed graph state");
    }
    free(before);
    free(after);
    osprey_bp_result_free(result);
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_fixed_message_failure_matrix(void)
{
    static const char *const family_names[] = {
        "variable-to-factor current corruption",
        "factor-to-variable current corruption",
        "variable-to-factor next corruption",
        "factor-to-variable next corruption"
    };
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x1b1);
    uint32_t id = add_primitive(ctx, region, 0);
    OspreyBpGraph *graph = NULL;
    OspreyBpResult *result = NULL;
    OspreyStatus status;

    add_prior(ctx, id, 0.5);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "message-family failure graph builds");
    if (graph != NULL) {
        double saved_vf[2];
        double saved_fv[2];
        double saved_next_vf[2];
        double saved_next_fv[2];
        double saved_beliefs[2];
        double *families[] = {
            graph->msg_vf_current, graph->msg_fv_current,
            graph->msg_vf_next, graph->msg_fv_next
        };
        double *saved_pointers[] = {
            graph->msg_vf_current, graph->msg_fv_current,
            graph->msg_vf_next, graph->msg_fv_next
        };
        memcpy(saved_vf, graph->msg_vf_current, sizeof(saved_vf));
        memcpy(saved_fv, graph->msg_fv_current, sizeof(saved_fv));
        memcpy(saved_next_vf, graph->msg_vf_next, sizeof(saved_next_vf));
        memcpy(saved_next_fv, graph->msg_fv_next, sizeof(saved_next_fv));
        memcpy(saved_beliefs, graph->beliefs, sizeof(saved_beliefs));
        for (unsigned family = 0; family < G_N_ELEMENTS(families);
             family++) {
            unsigned corruption_count = family < 2u ? 2u : 1u;
            for (unsigned corruption = 0; corruption < corruption_count;
                 corruption++) {
                double corrupt_value = family < 2u && corruption == 0u
                    ? NAN : INFINITY;
                memcpy(graph->msg_vf_current, saved_vf,
                       sizeof(saved_vf));
                memcpy(graph->msg_fv_current, saved_fv,
                       sizeof(saved_fv));
                memcpy(graph->msg_vf_next, saved_next_vf,
                       sizeof(saved_next_vf));
                memcpy(graph->msg_fv_next, saved_next_fv,
                       sizeof(saved_next_fv));
                memcpy(graph->beliefs, saved_beliefs,
                       sizeof(saved_beliefs));
                families[family][0] = corrupt_value;
                result = NULL;
                status = osprey_bp_solve_fixed(ctx, graph, &result);
                CHECK(status == OSPREY_INVALID_GRAPH && result == NULL,
                      family_names[family]);
                bool preserved =
                    graph->msg_vf_current == saved_pointers[0] &&
                    graph->msg_fv_current == saved_pointers[1] &&
                    graph->msg_vf_next == saved_pointers[2] &&
                    graph->msg_fv_next == saved_pointers[3] &&
                    graph->message_state == OSPREY_BP_MESSAGES_INITIAL &&
                    memcmp(graph->beliefs, saved_beliefs,
                           sizeof(saved_beliefs)) == 0;
                for (unsigned other = 0; other < G_N_ELEMENTS(families);
                     other++) {
                    if (other == family) continue;
                    const double *saved = other == 0u ? saved_vf :
                        other == 1u ? saved_fv :
                        other == 2u ? saved_next_vf : saved_next_fv;
                    preserved = preserved &&
                        memcmp(families[other], saved, sizeof(saved_vf)) == 0;
                }
                CHECK(preserved, "message-family rejection is atomic");
                /* The selected corruption is deliberately still present:
                 * pre-validation must not silently repair caller state. */
                CHECK((isnan(corrupt_value) &&
                       isnan(families[family][0])) ||
                          (isinf(corrupt_value) &&
                           isinf(families[family][0])),
                      "message-family rejection does not rewrite input");
            }
        }
        memcpy(graph->msg_vf_current, saved_vf, sizeof(saved_vf));
        memcpy(graph->msg_fv_current, saved_fv, sizeof(saved_fv));
        memcpy(graph->msg_vf_next, saved_next_vf, sizeof(saved_next_vf));
        memcpy(graph->msg_fv_next, saved_next_fv, sizeof(saved_next_fv));
        memcpy(graph->beliefs, saved_beliefs, sizeof(saved_beliefs));
        CHECK(osprey_bp_graph_validate(ctx, graph),
              "message-family failure matrix restores valid state");
    }
    osprey_bp_result_free(result);
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_fixed_convergence_policy(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x1c0);
    uint32_t id = add_primitive(ctx, region, 0);
    OspreyBpGraph *graph = NULL;
    OspreyBpResult *result = NULL;

    add_prior(ctx, id, 0.8);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "one-prior convergence-policy graph builds");
    if (graph != NULL) {
        CHECK(osprey_bp_solve_fixed(ctx, graph, &result) == OSPREY_OK &&
                  result != NULL && result->status == OSPREY_OK,
              "one-prior graph converges");
        if (result != NULL) {
            double belief = g_array_index(result->beliefs, double, 0);
            CHECK(result->iterations == 28u && result->stable_rounds == 10u &&
                      result->final_max_delta < 1e-6,
                  "solver stops at the exact ten-round policy boundary");
            CHECK(double_bits(result->final_max_delta) ==
                      UINT64_C(0x3e13333320000000) &&
                      double_bits(result->best_max_delta) ==
                      UINT64_C(0x3e13333320000000) &&
                      result->best_iteration == 28u,
                  "policy-bound diagnostics retain exact delta bits");
            CHECK(fabs(belief - 0.8) <= 2e-9,
                  "policy-bound one-prior belief remains numerically bounded");
        }
    }
    osprey_bp_result_free(result);
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_fixed_horn_support(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x1d0);
    uint32_t ids[3];
    uint32_t antecedent;
    OspreyBpGraph *graph = NULL;
    OspreyBpResult *result = NULL;
    char *before = NULL;
    char *after = NULL;

    for (uint32_t i = 0; i < G_N_ELEMENTS(ids); i++) {
        ids[i] = add_primitive(ctx, region, (int64_t)i * 8);
    }
    add_prior(ctx, ids[0], 1.0);
    antecedent = ids[0];
    add_implication_probability(ctx, OSPREY_RULE_CB01,
                                OSPREY_GRAPH_SECONDARY, false, 1.0,
                                &antecedent, 1, ids[1]);
    antecedent = ids[1];
    add_implication_probability(ctx, OSPREY_RULE_CB02,
                                OSPREY_GRAPH_SECONDARY, false, 1.0,
                                &antecedent, 1, ids[2]);
    antecedent = ids[0];
    add_implication_probability(ctx, OSPREY_RULE_CB03,
                                OSPREY_GRAPH_SECONDARY, false, 0.0,
                                &antecedent, 1, ids[2]);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "Horn-support contradiction graph builds");
    if (graph != NULL) {
        before = dump_graph(ctx, graph);
        CHECK(osprey_bp_solve_fixed(ctx, graph, &result) ==
                  OSPREY_INVALID_MODEL && result != NULL &&
                  result->status == OSPREY_INVALID_MODEL &&
                  result->iterations == 0,
              "linear Horn propagation rejects global hard conflict pre-round");
        after = dump_graph(ctx, graph);
        CHECK(before != NULL && after != NULL && strcmp(before, after) == 0,
              "hard-support rejection restores every BP buffer");
    }
    free(before);
    free(after);
    osprey_bp_result_free(result);
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
}

static void test_fixed_real_nonconvergence(void)
{
    OspreyContext *ctx = new_context();
    OspreyContext *permuted_ctx = NULL;
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x1e0);
    uint32_t ids[7];
    OspreyBpGraph *graph = NULL;
    OspreyBpGraph *permuted_graph = NULL;
    OspreyBpResult *result = NULL;
    OspreyBpResult *permuted_result = NULL;
    char *before = NULL;
    char *after = NULL;
    char *permuted_before = NULL;
    char *permuted_after = NULL;

    for (uint32_t i = 0; i < G_N_ELEMENTS(ids); i++) {
        ids[i] = add_primitive(ctx, region, (int64_t)i * 8);
    }
    add_prior(ctx, ids[0], 0.9);
    add_prior(ctx, ids[2], 0.01);
    add_prior(ctx, ids[3], 0.1);
    add_prior(ctx, ids[4], 0.9);
    add_prior(ctx, ids[5], 0.99);
    add_prior(ctx, ids[6], 0.1);

#define ADD_FIXTURE_IMPLICATION(_p, _head, ...) do {                       \
    uint32_t fixture_antecedents[] = { __VA_ARGS__ };                      \
    add_implication_probability(                                           \
        ctx, OSPREY_RULE_CB01, OSPREY_GRAPH_SECONDARY, false, (_p),       \
        fixture_antecedents, G_N_ELEMENTS(fixture_antecedents), (_head));  \
} while (0)
    ADD_FIXTURE_IMPLICATION(0.01, ids[4], ids[1], ids[0]);
    ADD_FIXTURE_IMPLICATION(0.2, ids[3], ids[0]);
    ADD_FIXTURE_IMPLICATION(0.999, ids[2], ids[0]);
    ADD_FIXTURE_IMPLICATION(0.999, ids[2], ids[0], ids[1]);
    ADD_FIXTURE_IMPLICATION(0.2, ids[5], ids[0]);
    ADD_FIXTURE_IMPLICATION(0.999, ids[2], ids[3], ids[1]);
    ADD_FIXTURE_IMPLICATION(0.99, ids[3], ids[6], ids[4], ids[2]);
    ADD_FIXTURE_IMPLICATION(0.1, ids[0], ids[5]);
    ADD_FIXTURE_IMPLICATION(0.9, ids[0], ids[2], ids[1]);
    ADD_FIXTURE_IMPLICATION(0.99, ids[2], ids[4]);
    ADD_FIXTURE_IMPLICATION(0.2, ids[5], ids[0], ids[1]);
    ADD_FIXTURE_IMPLICATION(0.9, ids[0], ids[2]);
    ADD_FIXTURE_IMPLICATION(0.001, ids[5], ids[0]);
    ADD_FIXTURE_IMPLICATION(0.01, ids[2], ids[3], ids[5]);
    ADD_FIXTURE_IMPLICATION(0.99, ids[2], ids[5]);
#undef ADD_FIXTURE_IMPLICATION

    permuted_ctx = reverse_clone_context(ctx);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL &&
              permuted_ctx != NULL &&
              osprey_bp_graph_build(permuted_ctx, &permuted_graph) ==
                  OSPREY_OK && permuted_graph != NULL,
          "both real-policy nonconvergence permutations build");
    if (graph != NULL && permuted_graph != NULL) {
        before = dump_graph(ctx, graph);
        permuted_before = dump_graph(permuted_ctx, permuted_graph);
        CHECK(osprey_bp_solve_fixed(ctx, graph, &result) ==
                  OSPREY_NON_CONVERGED && result != NULL &&
                  result->status == OSPREY_NON_CONVERGED,
              "frustrated loopy graph misses the actual 500-round policy");
        CHECK(osprey_bp_solve_fixed(permuted_ctx, permuted_graph,
                                    &permuted_result) ==
                  OSPREY_NON_CONVERGED && permuted_result != NULL &&
                  fixed_result_metadata_equal(result, permuted_result),
              "nonconvergence is bit-identical after insertion reversal");
        if (result != NULL) {
            CHECK(result->iterations == 500u && result->stable_rounds < 10u &&
                      result->nonconverged_component == 0u &&
                      isfinite(result->final_max_delta) &&
                      result->final_max_delta >= 1e-6 &&
                      isfinite(result->best_max_delta) &&
                      result->best_iteration > 0u &&
                      result->best_iteration <= 500u,
                  "nonconverged result retains deterministic diagnostics");
            CHECK(double_bits(result->final_max_delta) ==
                      UINT64_C(0x3fa82f45d31d7484) &&
                      double_bits(result->best_max_delta) ==
                      UINT64_C(0x3f839ec166b01b20) &&
                      result->best_iteration == 467u,
                  "frustrated-loop diagnostics retain exact delta bits");
            CHECK(osprey_bp_commit_result(ctx, graph, result) ==
                      OSPREY_NON_CONVERGED,
                  "nonconverged result cannot publish beliefs");
        }
        after = dump_graph(ctx, graph);
        permuted_after = dump_graph(permuted_ctx, permuted_graph);
        CHECK(before != NULL && after != NULL && strcmp(before, after) == 0 &&
                  permuted_before != NULL && permuted_after != NULL &&
                  strcmp(permuted_before, permuted_after) == 0,
              "nonconvergence restores both initial graph permutations");
    }
    for (uint32_t i = 0; i < G_N_ELEMENTS(ids); i++) {
        const OspreyVar *variable = &g_array_index(ctx->graph->vars,
                                                   OspreyVar, ids[i]);
        CHECK(variable->belief_valid == 0 && variable->belief == 0.0,
              "nonconvergence leaves every production belief unpublished");
    }
    free(before);
    free(after);
    free(permuted_before);
    free(permuted_after);
    osprey_bp_result_free(result);
    osprey_bp_result_free(permuted_result);
    osprey_bp_graph_free(graph);
    osprey_bp_graph_free(permuted_graph);
    osprey_free(ctx);
    osprey_free(permuted_ctx);
}

static void test_generated_fixed_forests(void)
{
    unsigned generated = 0;
    double max_error = 0.0;
    unsigned max_error_sample = 0;

    for (unsigned sample = 0; sample < 2000; sample++) {
        OspreyContext *ctx = generated_forest_context(sample);
        OspreyContext *permuted_ctx = NULL;
        OspreyBpGraph *graph = NULL;
        OspreyBpGraph *permuted_graph = NULL;
        OspreyBpResult *result = NULL;
        OspreyBpResult *permuted_result = NULL;
        double *expected = NULL;
        char *graph_dump = NULL;
        char *permuted_dump = NULL;
        OspreyStatus status = OSPREY_INVALID_GRAPH;
        OspreyStatus permuted_status = OSPREY_INVALID_GRAPH;
        bool ok = true;

        if (ctx == NULL) {
            ok = false;
        } else {
            permuted_ctx = reverse_clone_context(ctx);
            status = osprey_bp_graph_build(ctx, &graph);
            permuted_status = permuted_ctx == NULL
                ? OSPREY_INVALID_GRAPH
                : osprey_bp_graph_build(permuted_ctx, &permuted_graph);
            if (status != OSPREY_OK || permuted_status != OSPREY_OK ||
                graph == NULL || permuted_graph == NULL ||
                !osprey_bp_graph_validate(ctx, graph) ||
                !osprey_bp_graph_validate(permuted_ctx, permuted_graph) ||
                graph->vars->len != permuted_graph->vars->len) {
                ok = false;
            }
        }
        if (ok) {
            expected = g_new(double, graph->vars->len);
            ok = brute_force_beliefs(ctx, graph, expected);
        }
        if (ok) {
            status = osprey_bp_solve_fixed(ctx, graph, &result);
            permuted_status = osprey_bp_solve_fixed(
                permuted_ctx, permuted_graph, &permuted_result);
            if (status != OSPREY_OK || permuted_status != OSPREY_OK ||
                result == NULL || permuted_result == NULL ||
                result->status != OSPREY_OK ||
                permuted_result->status != OSPREY_OK ||
                !fixed_result_metadata_equal(result, permuted_result) ||
                result->beliefs->len != graph->vars->len ||
                result->stable_rounds != 10u ||
                result->nonconverged_component != UINT32_MAX) {
                ok = false;
            }
        }
        if (ok) {
            graph_dump = dump_graph(ctx, graph);
            permuted_dump = dump_graph(permuted_ctx, permuted_graph);
            if (graph_dump == NULL || permuted_dump == NULL ||
                strcmp(graph_dump, permuted_dump) != 0) {
                size_t mismatch = 0;
                if (graph_dump != NULL && permuted_dump != NULL) {
                    while (graph_dump[mismatch] == permuted_dump[mismatch] &&
                           graph_dump[mismatch] != '\0' &&
                           permuted_dump[mismatch] != '\0') mismatch++;
                }
                fprintf(stderr, "fixed forest dump mismatch seed %u at %zu "
                        "chars %02x/%02x\n", sample, mismatch,
                        graph_dump == NULL ? 0 :
                            (unsigned char)graph_dump[mismatch],
                        permuted_dump == NULL ? 0 :
                            (unsigned char)permuted_dump[mismatch]);
                ok = false;
            }
        }
        if (ok) {
            for (guint local = 0; local < result->beliefs->len; local++) {
                double actual = g_array_index(result->beliefs, double, local);
                double error = fabs(actual - expected[local]);
                if (!isfinite(actual) || actual < 0.0 || actual > 1.0 ||
                    !isfinite(error) ||
                    error > OSPREY_BP_FOREST_ORACLE_TOL) {
                    fprintf(stderr, "oracle mismatch local %u actual %a "
                            "expected %a error %a\n", local, actual,
                            expected[local], error);
                    ok = false;
                    break;
                }
                if (error > max_error) {
                    max_error = error;
                    max_error_sample = sample;
                }
            }
        }
        if (!ok) {
            fprintf(stderr, "fixed forest checks seed %u status %d/%d "
                    "result %p/%p metadata %d\n", sample, status,
                    permuted_status, (void *)result, (void *)permuted_result,
                    fixed_result_metadata_equal(result, permuted_result) ? 1 : 0);
            if (result != NULL && permuted_result != NULL &&
                result->beliefs != NULL && permuted_result->beliefs != NULL) {
                for (guint i = 0; i < result->beliefs->len &&
                                  i < permuted_result->beliefs->len; i++) {
                    if (double_bits(g_array_index(result->beliefs, double, i)) !=
                        double_bits(g_array_index(permuted_result->beliefs,
                                                  double, i))) {
                        fprintf(stderr, "belief mismatch local %u %016llx/%016llx\n",
                                i,
                                (unsigned long long)double_bits(
                                    g_array_index(result->beliefs, double, i)),
                                (unsigned long long)double_bits(
                                    g_array_index(permuted_result->beliefs,
                                                  double, i)));
                        break;
                    }
                }
            }
            dump_fixed_solver_failure(sample, ctx, graph, result);
            if (permuted_ctx != NULL && permuted_graph != NULL) {
                dump_fixed_solver_failure(sample, permuted_ctx,
                                          permuted_graph, permuted_result);
            }
        } else {
            generated++;
        }
        free(graph_dump);
        free(permuted_dump);
        g_free(expected);
        osprey_bp_result_free(result);
        osprey_bp_result_free(permuted_result);
        osprey_bp_graph_free(graph);
        osprey_bp_graph_free(permuted_graph);
        osprey_free(ctx);
        osprey_free(permuted_ctx);
    }
    fprintf(stderr, "fixed forest corpus: generated %u/2000 max-error %a "
            "sample %u bits %016llx\n", generated, max_error,
            max_error_sample, (unsigned long long)double_bits(max_error));
    CHECK(generated == 2000,
          "all 2000 generated fixed forests converge in both permutations");
    CHECK(max_error <= OSPREY_BP_FOREST_ORACLE_TOL,
          "generated fixed-forest beliefs meet the policy-bounded oracle");
}

static void test_generated_projections(void)
{
    uint32_t state = 0x5eeda11u;
    unsigned generated = 0;

    for (unsigned sample = 0; sample < 2000; sample++) {
        OspreyContext *ctx = new_context();
        OspreyContext *permuted_ctx = NULL;
        OspreyRegionId region = make_region(
            (next_random(&state) & 1u) ? OSPREY_REGION_GLOBAL
                                       : OSPREY_REGION_STACK_FUNCTION,
            0x100 + sample);
        uint32_t count = 1 + next_random(&state) % 12;
        uint32_t ids[12];
        uint32_t order[12];
        OspreyBpGraph *graph = NULL;
        OspreyBpGraph *permuted_graph = NULL;
        char *graph_dump = NULL;
        char *permuted_dump = NULL;
        bool ok = true;

        for (uint32_t i = 0; i < count; i++) order[i] = i;
        for (uint32_t i = count; i > 1; i--) {
            uint32_t selected = next_random(&state) % i;
            uint32_t swap = order[i - 1];
            order[i - 1] = order[selected];
            order[selected] = swap;
        }
        for (uint32_t position = 0; position < count; position++) {
            uint32_t i = order[position];
            double probability = generated_probability(next_random(&state));
            ids[i] = add_primitive(ctx, region,
                                   (int64_t)i * 8 - (int64_t)(sample & 3u) * 8);
            set_seed(ctx, ids[i], probability);
            ok = add_prior(ctx, ids[i], probability) && ok;
        }
        if (count >= 2) {
            uint32_t antecedent = ids[0];
            ok = add_implication_probability(
                ctx, OSPREY_RULE_CB01, OSPREY_GRAPH_SECONDARY,
                (next_random(&state) & 1u) != 0,
                generated_probability(next_random(&state)), &antecedent, 1,
                ids[1]) && ok;
        }
        if (count >= 3) {
            uint32_t antecedents[2] = { ids[0], ids[1] };
            ok = add_implication_probability(
                ctx, OSPREY_RULE_CB02, OSPREY_GRAPH_SECONDARY, false,
                generated_probability(next_random(&state)), antecedents, 2,
                ids[2]) && ok;
        }
        if (count >= 4) {
            uint32_t antecedents[3] = { ids[0], ids[1], ids[2] };
            ok = add_implication_probability(
                ctx, OSPREY_RULE_CB03, OSPREY_GRAPH_SECONDARY, false,
                generated_probability(next_random(&state)), antecedents, 3,
                ids[3]) && ok;
        }
        if (sample % 19u == 0) {
            OspreyFactorResult hard = osprey_factor_add_hard_false(
                ctx, OSPREY_RULE_CB06, OSPREY_GRAPH_SECONDARY,
                ids[count - 1]);
            CHECK(hard.status == OSPREY_OK,
                  "generated hard-false factor inserted");
            ok = hard.status == OSPREY_OK && ok;
        }
        permuted_ctx = reverse_clone_context(ctx);
        OspreyStatus status = osprey_bp_graph_build(ctx, &graph);
        OspreyStatus permuted_status = permuted_ctx == NULL
            ? OSPREY_INVALID_GRAPH
            : osprey_bp_graph_build(permuted_ctx, &permuted_graph);
        bool production_valid = graph != NULL &&
            osprey_bp_graph_validate(ctx, graph);
        bool reference_valid = graph != NULL &&
            stage5_bp_reference_matches(ctx, graph);
        bool permuted_valid = permuted_graph != NULL &&
            osprey_bp_graph_validate(permuted_ctx, permuted_graph) &&
            stage5_bp_reference_matches(permuted_ctx, permuted_graph);
        if (status == OSPREY_OK && permuted_status == OSPREY_OK &&
            production_valid && reference_valid && permuted_valid) {
            graph_dump = dump_graph(ctx, graph);
            permuted_dump = dump_graph(permuted_ctx, permuted_graph);
        }
        if (status != OSPREY_OK || permuted_status != OSPREY_OK ||
            graph == NULL || permuted_graph == NULL || !production_valid ||
            !reference_valid || !permuted_valid || graph_dump == NULL ||
            permuted_dump == NULL || strcmp(graph_dump, permuted_dump) != 0) {
            fprintf(stderr, "generated projection mismatch at seed %u "
                    "status %d/%d vars %u factors %u components %u/%u "
                    "valid %d/%d ref %d\n", sample, status,
                    permuted_status, ctx->graph->vars->len,
                    ctx->graph->factors->len,
                    graph == NULL ? 0 : graph->components->len,
                    permuted_graph == NULL ? 0 : permuted_graph->components->len,
                    production_valid ? 1 : 0, permuted_valid ? 1 : 0,
                    reference_valid ? 1 : 0);
            ok = false;
        }
        if (ok) {
            /* Give both canonical projections identical arbitrary current
             * messages; their next buffers must remain identical despite
             * reversing every source variable and factor insertion. */
            for (guint edge_id = 0; edge_id < graph->edges->len; edge_id++) {
                size_t index = (size_t)edge_id * 2u;
                double vf_probability =
                    (double)(next_random(&state) % 1000u + 1u) / 1001.0;
                double fv_probability =
                    (double)(next_random(&state) % 1000u + 1u) / 1001.0;
                set_log_probability_pair(&graph->msg_vf_current[index],
                                         vf_probability);
                set_log_probability_pair(&graph->msg_fv_current[index],
                                         fv_probability);
                set_log_probability_pair(
                    &permuted_graph->msg_vf_current[index], vf_probability);
                set_log_probability_pair(
                    &permuted_graph->msg_fv_current[index], fv_probability);
            }
            ok = compare_round_with_reference(ctx, graph, OSPREY_OK) &&
                 compare_round_with_reference(permuted_ctx, permuted_graph,
                                              OSPREY_OK) && ok;
            if (ok) {
                for (uint64_t i = 0; i < graph->message_values; i++) {
                    if (graph->msg_vf_next[(size_t)i] !=
                            permuted_graph->msg_vf_next[(size_t)i] ||
                        graph->msg_fv_next[(size_t)i] !=
                            permuted_graph->msg_fv_next[(size_t)i]) {
                        ok = false;
                        break;
                    }
                }
            }
        }
        if (!ok) {
            dump_generated_round_failure(sample, ctx, graph);
            dump_generated_round_failure(sample, permuted_ctx,
                                         permuted_graph);
        } else {
            generated++;
        }
        free(graph_dump);
        free(permuted_dump);
        osprey_bp_graph_free(graph);
        osprey_bp_graph_free(permuted_graph);
        osprey_free(ctx);
        osprey_free(permuted_ctx);
    }
    CHECK(generated == 2000,
          "all 2000 generated projection and round cases execute");
}

int main(void)
{
    RUN(test_bp_configuration);
    RUN(test_basic_projection);
    RUN(test_arity_and_components);
    RUN(test_cross_region_bridge);
    RUN(test_exact_seed_values);
    RUN(test_secondary_uniform_seed);
    RUN(test_round_unary_boundaries);
    RUN(test_round_implication_roles);
    RUN(test_round_arity_three_four);
    RUN(test_round_hard_false);
    RUN(test_round_recipient_exclusion);
    RUN(test_round_failure_paths);
    RUN(test_round_validation_boundaries);
    RUN(test_permutation_dump);
    RUN(test_malformed_inputs);
    RUN(test_reverse_adjacency_validation);
    RUN(test_component_maximality_validation);
    RUN(test_workspace_boundaries);
    RUN(test_allocation_failures);
    RUN(test_rebuild_after_failure);
    RUN(test_fixed_damping);
    RUN(test_fixed_graph_solver);
    RUN(test_fixed_solver_failures);
    RUN(test_fixed_workspace_failure);
    RUN(test_fixed_message_failure_matrix);
    RUN(test_fixed_convergence_policy);
    RUN(test_fixed_horn_support);
    RUN(test_fixed_real_nonconvergence);
    RUN(test_generated_fixed_forests);
    RUN(test_generated_projections);

    if (failures != 0 || executed != registered) {
        fprintf(stderr, "FAIL stage5_bp (%u failures, %u/%u)\n",
                failures, executed, registered);
        return 1;
    }
    printf("PASS stage5_bp (%u/%u; fixed forests 2000/2000; "
           "projections 2000/2000)\n", executed, registered);
    return 0;
}
