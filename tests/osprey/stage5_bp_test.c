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
#define OSPREY_BP_LOOPY_CORPUS_CASES 256u
#define OSPREY_BP_LOOPY_TRACE_ROUNDS 16u

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

static uint32_t add_primitive_sized(OspreyContext *ctx,
                                    OspreyRegionId region, int64_t offset,
                                    uint64_t size)
{
    OspreyVarPayload payload;
    OspreyInternResult result;
    memset(&payload, 0, sizeof(payload));
    payload.chunk = make_chunk(region, offset, size);
    result = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR, &payload);
    CHECK(result.id != UINT32_MAX, "sized primitive variable inserted");
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

static uint32_t add_unfoldable(OspreyContext *ctx, OspreyRegionId region,
                                uint64_t size)
{
    OspreyVarPayload payload;
    OspreyInternResult result;
    memset(&payload, 0, sizeof(payload));
    payload.heap_fold.region = region;
    payload.heap_fold.size = size;
    result = osprey_intern_var(ctx, OSPREY_PRED_UNFOLDABLE_HEAP, &payload);
    CHECK(result.id != UINT32_MAX, "unfoldable variable inserted");
    return result.id;
}

static uint32_t add_homo(OspreyContext *ctx, OspreyRegionId region,
                         int64_t first_offset, int64_t second_offset,
                         int64_t size)
{
    OspreyVarPayload payload;
    OspreyInternResult result;
    memset(&payload, 0, sizeof(payload));
    payload.segment.a1.region = region;
    payload.segment.a1.offset = first_offset;
    payload.segment.a2.region = region;
    payload.segment.a2.offset = second_offset;
    payload.segment.size = size;
    result = osprey_intern_var(ctx, OSPREY_PRED_HOMO_SEGMENT, &payload);
    CHECK(result.id != UINT32_MAX, "homomorphic segment inserted");
    return result.id;
}

static void add_region_extent(OspreyContext *ctx, OspreyRegionId region,
                              uint64_t high)
{
    OspreyRegionInstance instance;
    memset(&instance, 0, sizeof(instance));
    instance.region = region;
    instance.instance_id = 1;
    instance.raw_base = 0;
    instance.raw_min = 0;
    instance.raw_max = high;
    instance.sample_support = 1;
    g_array_append_val(ctx->region_instances, instance);
}

static void add_access_chunk(OspreyContext *ctx, OspreyChunk chunk)
{
    OspreyAccessFact fact;
    memset(&fact, 0, sizeof(fact));
    fact.chunk = chunk;
    fact.sample_support = 1;
    g_array_append_val(ctx->access_facts, fact);
}

static void add_logical_access(OspreyContext *ctx, uint64_t pc,
                               OspreyChunk chunk)
{
    OspreyLogicalAccess access;
    memset(&access, 0, sizeof(access));
    access.pc = pc;
    access.chunk = chunk;
    access.dynamic_count = 1;
    access.sample_support = 1;
    g_array_append_val(ctx->logical_access_facts, access);
}

static unsigned graph_rule_count(const OspreyContext *ctx,
                                 const OspreyBpGraph *graph, uint16_t rule)
{
    unsigned count = 0;
    if (ctx == NULL || ctx->graph == NULL || graph == NULL ||
        graph->factors == NULL) return 0;
    for (guint local = 0; local < graph->factors->len; local++) {
        const OspreyBpFactorRef *ref = &g_array_index(
            graph->factors, OspreyBpFactorRef, local);
        if (ref->graph_factor_id >= ctx->graph->factors->len) continue;
        const OspreyFactor *factor = g_array_index(
            ctx->graph->factors, OspreyFactor *, ref->graph_factor_id);
        if (factor != NULL && factor->rule == rule) count++;
    }
    return count;
}

static bool graph_has_variable_kind(const OspreyContext *ctx,
                                    const OspreyBpGraph *graph,
                                    uint8_t kind)
{
    if (ctx == NULL || ctx->graph == NULL || graph == NULL ||
        graph->vars == NULL) return false;
    for (guint local = 0; local < graph->vars->len; local++) {
        const OspreyBpVarRef *ref = &g_array_index(
            graph->vars, OspreyBpVarRef, local);
        if (ref->graph_var_id < ctx->graph->vars->len &&
            g_array_index(ctx->graph->vars, OspreyVar,
                          ref->graph_var_id).kind == kind) return true;
    }
    return false;
}

static bool graph_messages_unchanged(const OspreyBpGraph *graph,
                                     const double *vf, const double *fv)
{
    if (graph == NULL || vf == NULL || fv == NULL) return false;
    return memcmp(graph->msg_vf_current, vf,
                  (size_t)graph->message_values * sizeof(double)) == 0 &&
           memcmp(graph->msg_fv_current, fv,
                  (size_t)graph->message_values * sizeof(double)) == 0;
}

static bool graph_next_buffers_poisoned(const OspreyBpGraph *graph)
{
    if (graph == NULL || graph->msg_vf_next == NULL ||
        graph->msg_fv_next == NULL || graph->scratch_message == NULL) {
        return false;
    }
    for (uint64_t i = 0; i < graph->message_values; i++) {
        if (!isnan(graph->msg_vf_next[i]) ||
            !isnan(graph->msg_fv_next[i]) ||
            !isnan(graph->scratch_message[i])) return false;
    }
    return true;
}

static uint32_t edge_graph_factor_id(const OspreyBpGraph *graph,
                                     uint32_t edge_id)
{
    if (graph == NULL || graph->edges == NULL || graph->factors == NULL ||
        edge_id >= graph->edges->len) return UINT32_MAX;
    const OspreyBpEdge *edge = &g_array_index(graph->edges, OspreyBpEdge,
                                               edge_id);
    if (edge->local_factor >= graph->factors->len) return UINT32_MAX;
    return g_array_index(graph->factors, OspreyBpFactorRef,
                         edge->local_factor).graph_factor_id;
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

static void dump_generated_initial_state(unsigned sample,
                                         OspreyContext *ctx,
                                         const char *label)
{
    OspreyBpGraph *initial = NULL;
    OspreyStatus status;

    fprintf(stderr, "INITIAL %s\n", label == NULL ? "GRAPH" : label);
    status = ctx == NULL ? OSPREY_INVALID_GRAPH
        : osprey_bp_graph_build(ctx, &initial);
    if (status == OSPREY_OK && initial != NULL) {
        dump_generated_round_failure(sample, ctx, initial);
    } else {
        fprintf(stderr, "initial BP build failed with status %d\n", status);
        if (ctx != NULL && ctx->graph != NULL) {
            osprey_graph_dump_file(ctx, stderr);
        }
    }
    osprey_bp_graph_free(initial);
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

static double generated_loopy_probability(uint32_t value)
{
    static const double probabilities[] = {
        0.07, 0.13, 0.23, 0.31, 0.43,
        0.57, 0.69, 0.77, 0.87, 0.93
    };
    return probabilities[value % G_N_ELEMENTS(probabilities)];
}

static OspreyContext *generated_loopy_context(unsigned sample)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL,
                                        0x300u + sample);
    uint32_t state = 0x31415927u ^ (sample * 0x9e3779b9u);
    uint32_t ids[9];
    uint32_t order[9];
    uint32_t count;

    if (ctx == NULL) return NULL;
    count = 3u + next_random(&state) % 7u;
    for (uint32_t i = 0; i < count; i++) order[i] = i;
    for (uint32_t i = count; i > 1; i--) {
        uint32_t selected = next_random(&state) % i;
        uint32_t swap = order[i - 1u];
        order[i - 1u] = order[selected];
        order[selected] = swap;
    }
    for (uint32_t position = 0; position < count; position++) {
        uint32_t semantic_id = order[position];
        double probability = generated_loopy_probability(
            next_random(&state));
        ids[semantic_id] = add_primitive(ctx, region,
                                         (int64_t)semantic_id * 16);
        set_seed(ctx, ids[semantic_id], probability);
        if (!add_prior(ctx, ids[semantic_id], probability)) goto fail;
    }
    for (uint32_t i = 0; i < count; i++) {
        uint32_t antecedent = ids[i];
        uint16_t rule = (uint16_t)(OSPREY_RULE_CB01 + i);
        if (!add_implication_probability(
                ctx, rule, OSPREY_GRAPH_SECONDARY, false,
                generated_loopy_probability(next_random(&state)),
                &antecedent, 1, ids[(i + 1u) % count])) goto fail;
    }
    if (count >= 5u) {
        for (uint32_t i = 0; i < 2u; i++) {
            uint32_t antecedents[2] = { ids[i], ids[i + 1u] };
            if (!add_implication_probability(
                    ctx, (uint16_t)(OSPREY_RULE_CC01 + i),
                    OSPREY_GRAPH_SECONDARY, false,
                    generated_loopy_probability(next_random(&state)),
                    antecedents, 2, ids[(i + 3u) % count])) goto fail;
        }
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
                                      OspreyContext *ctx,
                                      const OspreyBpGraph *graph,
                                      const OspreyBpResult *result)
{
    fprintf(stderr, "fixed forest failure seed %u\n", sample);
    dump_generated_initial_state(sample, ctx, "FIXED");
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

static bool explicit_logaddexp(double left, double right, double *out)
{
    double high;
    double low;
    double value;

    if (out == NULL ||
        ((!isfinite(left)) && left != -INFINITY) ||
        ((!isfinite(right)) && right != -INFINITY)) return false;
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

static bool explicit_damped_pair(const double current[2],
                                 const double raw[2], double out[2])
{
    double mixed[2];
    double norm;

    if (current == NULL || raw == NULL || out == NULL) return false;
    for (unsigned state = 0; state < 2; state++) {
        double current_term = log(0.5) + current[state];
        double raw_term = log1p(-0.5) + raw[state];
        if (!explicit_logaddexp(current_term, raw_term, &mixed[state])) {
            return false;
        }
    }
    if ((mixed[0] == -INFINITY && mixed[1] == -INFINITY) ||
        !explicit_logaddexp(mixed[0], mixed[1], &norm) ||
        !isfinite(norm)) return false;
    for (unsigned state = 0; state < 2; state++) {
        out[state] = mixed[state] == -INFINITY
            ? -INFINITY : mixed[state] - norm;
        if (out[state] != -INFINITY &&
            (!isfinite(out[state]) || out[state] > 0.0)) return false;
    }
    return true;
}

static void test_swap_damped_buffers(OspreyBpGraph *graph)
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

static OspreyStatus reference_raw_round_copy(
    const OspreyContext *ctx, const OspreyBpGraph *graph,
    const double *vf_current, const double *fv_current, double *vf_next,
    double *fv_next)
{
    OspreyBpMessages messages;

    if (ctx == NULL || graph == NULL || vf_current == NULL ||
        fv_current == NULL || vf_next == NULL || fv_next == NULL) {
        return OSPREY_INVALID_GRAPH;
    }
    messages.vf_current = (double *)vf_current;
    messages.vf_next = vf_next;
    messages.fv_current = (double *)fv_current;
    messages.fv_next = fv_next;
    messages.value_count = graph->message_values;
    return stage5_bp_reference_compute_round(ctx, graph, &messages);
}

static bool message_pair_bits_equal(const double left[2],
                                    const double right[2])
{
    return double_bits(left[0]) == double_bits(right[0]) &&
           double_bits(left[1]) == double_bits(right[1]);
}

static bool message_families_normalized(const OspreyBpGraph *graph,
                                        bool next)
{
    const double *vf;
    const double *fv;

    if (graph == NULL) return false;
    vf = next ? graph->msg_vf_next : graph->msg_vf_current;
    fv = next ? graph->msg_fv_next : graph->msg_fv_current;
    if (vf == NULL || fv == NULL || graph->edges == NULL) return false;
    for (guint edge_id = 0; edge_id < graph->edges->len; edge_id++) {
        size_t index = (size_t)edge_id * 2u;
        const double *vf_pair = &vf[index];
        const double *fv_pair = &fv[index];
        double vf_max = vf_pair[0] > vf_pair[1] ? vf_pair[0] : vf_pair[1];
        double fv_max = fv_pair[0] > fv_pair[1] ? fv_pair[0] : fv_pair[1];
        double vf_norm;
        double fv_norm;

        if ((vf_pair[0] == -INFINITY && vf_pair[1] == -INFINITY) ||
            (fv_pair[0] == -INFINITY && fv_pair[1] == -INFINITY) ||
            ((!isfinite(vf_pair[0])) && vf_pair[0] != -INFINITY) ||
            ((!isfinite(vf_pair[1])) && vf_pair[1] != -INFINITY) ||
            ((!isfinite(fv_pair[0])) && fv_pair[0] != -INFINITY) ||
            ((!isfinite(fv_pair[1])) && fv_pair[1] != -INFINITY)) {
            return false;
        }
        vf_norm = exp(vf_pair[0] - vf_max) + exp(vf_pair[1] - vf_max);
        fv_norm = exp(fv_pair[0] - fv_max) + exp(fv_pair[1] - fv_max);
        if (!isfinite(vf_norm) || !isfinite(fv_norm) ||
            fabs(vf_max + log(vf_norm)) > 1e-12 ||
            fabs(fv_max + log(fv_norm)) > 1e-12) return false;
    }
    return true;
}

static bool find_exact_tolerance_boundary(double tolerance,
                                          double *probability_out,
                                          double *candidate_out)
{
    double center = 3.0 * tolerance;

    if (probability_out == NULL || candidate_out == NULL) return false;
    for (unsigned direction = 0; direction < 2; direction++) {
        double probability = center;
        for (unsigned step = 0; step < 4096; step++) {
            double current_pair[2] = { 0.0, -INFINITY };
            double raw_pair[2];
            double candidate_pair[2];
            double candidate;
            double baseline;

            set_log_probability_pair(raw_pair, probability);
            if (explicit_damped_pair(current_pair, raw_pair,
                                     candidate_pair)) {
                candidate = exp(candidate_pair[1]);
                baseline = candidate - tolerance;
                if (baseline >= 0.0 && candidate > tolerance &&
                    candidate - baseline == tolerance) {
                    *probability_out = probability;
                    *candidate_out = candidate;
                    return true;
                }
            }
            probability = nextafter(
                probability, direction == 0 ? 0.0 : INFINITY);
        }
    }
    return false;
}

static uint64_t message_families_digest(const OspreyBpGraph *graph,
                                        bool next)
{
    const double *vf;
    const double *fv;
    uint64_t digest = UINT64_C(1469598103934665603);

    if (graph == NULL) return 0;
    vf = next ? graph->msg_vf_next : graph->msg_vf_current;
    fv = next ? graph->msg_fv_next : graph->msg_fv_current;
    if (vf == NULL || fv == NULL) return 0;
    for (unsigned family = 0; family < 2u; family++) {
        const double *values = family == 0u ? vf : fv;
        for (uint64_t i = 0; i < graph->message_values; i++) {
            uint64_t bits = double_bits(values[i]);
            digest ^= bits;
            digest *= UINT64_C(1099511628211);
        }
    }
    return digest;
}

static bool next_message_families_empty(const OspreyBpGraph *graph)
{
    if (graph == NULL || graph->msg_vf_next == NULL ||
        graph->msg_fv_next == NULL) return false;
    for (uint64_t i = 0; i < graph->message_values; i++) {
        if (!isnan(graph->msg_vf_next[i]) ||
            !isnan(graph->msg_fv_next[i])) return false;
    }
    return true;
}

static bool run_damped_trace_pair(
    const OspreyContext *ctx, OspreyBpGraph *graph,
    const OspreyContext *permuted_ctx, OspreyBpGraph *permuted_graph,
    bool *changed_out, uint64_t *trace_digests,
    uint64_t *permuted_trace_digests, unsigned *failed_round_out)
{
    bool changed = false;

    if (changed_out != NULL) *changed_out = false;
    if (failed_round_out != NULL) *failed_round_out = UINT32_MAX;
    if (ctx == NULL || graph == NULL || permuted_ctx == NULL ||
        permuted_graph == NULL || changed_out == NULL ||
        trace_digests == NULL || permuted_trace_digests == NULL ||
        failed_round_out == NULL ||
        graph->message_values != permuted_graph->message_values) return false;
    for (unsigned round = 0; round < OSPREY_BP_LOOPY_TRACE_ROUNDS;
         round++) {
        OspreyBpMessages messages = graph_messages(graph);
        OspreyBpMessages permuted_messages = graph_messages(permuted_graph);
        OspreyStatus status = osprey_bp_compute_round_damped(
            ctx, graph, &messages, NULL, 0.5);
        OspreyStatus permuted_status = osprey_bp_compute_round_damped(
            permuted_ctx, permuted_graph, &permuted_messages, NULL, 0.5);

        trace_digests[round] = message_families_digest(graph, true);
        permuted_trace_digests[round] = message_families_digest(
            permuted_graph, true);
        if (status != OSPREY_OK || permuted_status != OSPREY_OK ||
            !message_families_normalized(graph, true) ||
            !message_families_normalized(permuted_graph, true) ||
            trace_digests[round] != permuted_trace_digests[round] ||
            memcmp(graph->msg_vf_next, permuted_graph->msg_vf_next,
                   (size_t)graph->message_values * sizeof(double)) != 0 ||
            memcmp(graph->msg_fv_next, permuted_graph->msg_fv_next,
                   (size_t)graph->message_values * sizeof(double)) != 0) {
            *failed_round_out = round + 1u;
            return false;
        }
        if (memcmp(graph->msg_vf_current, graph->msg_vf_next,
                   (size_t)graph->message_values * sizeof(double)) != 0 ||
            memcmp(graph->msg_fv_current, graph->msg_fv_next,
                   (size_t)graph->message_values * sizeof(double)) != 0) {
            changed = true;
        }
        test_swap_damped_buffers(graph);
        test_swap_damped_buffers(permuted_graph);
        if (!message_families_normalized(graph, false) ||
            !message_families_normalized(permuted_graph, false) ||
            !next_message_families_empty(graph) ||
            !next_message_families_empty(permuted_graph)) {
            *failed_round_out = round + 1u;
            return false;
        }
    }
    *changed_out = changed;
    return true;
}

static void test_fixed_round_damping(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x1a1);
    uint32_t a = add_primitive(ctx, region, 0);
    uint32_t b = add_primitive(ctx, region, 8);
    uint32_t antecedent = a;
    OspreyBpGraph *graph = NULL;
    double *raw_vf = NULL;
    double *raw_fv = NULL;
    double *first_vf = NULL;
    double *first_fv = NULL;

    set_seed(ctx, a, 0.25);
    set_seed(ctx, b, 0.75);
    add_prior(ctx, a, 0.25);
    add_prior(ctx, b, 0.75);
    add_implication_probability(ctx, OSPREY_RULE_CB01,
                                OSPREY_GRAPH_SECONDARY, false, 0.9,
                                &antecedent, 1, b);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "graph-level damping fixture builds");
    if (graph != NULL) {
        uint32_t local_a = local_for_offset(ctx, graph, 0);
        uint32_t prior_edge = edge_for_local_rule(
            ctx, graph, local_a, OSPREY_RULE_CA01);
        OspreyBpMessages messages = graph_messages(graph);
        double raw_second[2];
        bool allocated = graph->message_values <= SIZE_MAX / sizeof(double);
        bool oracle_ok = true;
        size_t message_bytes = allocated
            ? (size_t)graph->message_values * sizeof(double) : 0;

        CHECK(local_a != UINT32_MAX && prior_edge != UINT32_MAX,
              "graph-level damping fixture resolves a unary edge");
        if (allocated) {
            raw_vf = g_new(double, (size_t)graph->message_values);
            raw_fv = g_new(double, (size_t)graph->message_values);
            first_vf = g_new(double, (size_t)graph->message_values);
            first_fv = g_new(double, (size_t)graph->message_values);
        }
        CHECK(allocated && raw_vf != NULL && raw_fv != NULL &&
                  first_vf != NULL && first_fv != NULL,
              "graph-level damping fixture allocates trace storage");
        if (allocated && raw_vf != NULL && raw_fv != NULL &&
            first_vf != NULL && first_fv != NULL &&
            local_a != UINT32_MAX && prior_edge != UINT32_MAX) {
            CHECK(reference_raw_round_copy(
                      ctx, graph, graph->msg_vf_current,
                      graph->msg_fv_current, raw_vf, raw_fv) == OSPREY_OK,
                  "graph-level damping obtains an independent raw first half-step");
            for (guint edge = 0; edge < graph->edges->len; edge++) {
                size_t index = (size_t)edge * 2u;
                oracle_ok = explicit_damped_pair(
                    &graph->msg_vf_current[index], &raw_vf[index],
                    &first_vf[index]) && oracle_ok;
            }
            oracle_ok = stage5_bp_reference_compute_factor_half(
                ctx, graph, first_vf, raw_fv) == OSPREY_OK && oracle_ok;
            for (guint edge = 0; edge < graph->edges->len; edge++) {
                size_t index = (size_t)edge * 2u;
                oracle_ok = explicit_damped_pair(
                    &graph->msg_fv_current[index], &raw_fv[index],
                    &first_fv[index]) && oracle_ok;
            }
            CHECK(oracle_ok,
                  "independent first staged-round oracle evaluates");
            CHECK(osprey_bp_compute_round_damped(
                      ctx, graph, &messages, NULL, 0.5) == OSPREY_OK,
                  "graph-level damping executes the first staged round");
            CHECK(memcmp(graph->msg_vf_next, first_vf, message_bytes) == 0 &&
                      memcmp(graph->msg_fv_next, first_fv,
                             message_bytes) == 0,
                  "first graph round matches both independently staged families");
            CHECK(message_families_normalized(graph, true),
                  "first staged round leaves every next pair normalized");
            test_swap_damped_buffers(graph);
            messages = graph_messages(graph);
            CHECK(reference_raw_round_copy(
                      ctx, graph, graph->msg_vf_current,
                      graph->msg_fv_current, raw_vf, raw_fv) == OSPREY_OK,
                  "graph-level damping obtains an independent raw second half-step");
            memcpy(raw_second, &raw_vf[(size_t)prior_edge * 2u],
                   sizeof(raw_second));
            oracle_ok = true;
            for (guint edge = 0; edge < graph->edges->len; edge++) {
                size_t index = (size_t)edge * 2u;
                oracle_ok = explicit_damped_pair(
                    &graph->msg_vf_current[index], &raw_vf[index],
                    &first_vf[index]) && oracle_ok;
            }
            oracle_ok = stage5_bp_reference_compute_factor_half(
                ctx, graph, first_vf, raw_fv) == OSPREY_OK && oracle_ok;
            for (guint edge = 0; edge < graph->edges->len; edge++) {
                size_t index = (size_t)edge * 2u;
                oracle_ok = explicit_damped_pair(
                    &graph->msg_fv_current[index], &raw_fv[index],
                    &first_fv[index]) && oracle_ok;
            }
            CHECK(oracle_ok,
                  "independent second staged-round oracle evaluates");
            CHECK(osprey_bp_compute_round_damped(
                      ctx, graph, &messages, NULL, 0.5) == OSPREY_OK,
                  "graph-level damping executes the second staged round");
            CHECK(memcmp(graph->msg_vf_next, first_vf, message_bytes) == 0 &&
                      memcmp(graph->msg_fv_next, first_fv,
                             message_bytes) == 0,
                  "second graph round matches both independently staged families");
            CHECK(!message_pair_bits_equal(
                      raw_second,
                      &graph->msg_vf_current[(size_t)prior_edge * 2u]) &&
                      !message_pair_bits_equal(
                          raw_second,
                          &graph->msg_vf_next[(size_t)prior_edge * 2u]),
                  "raw second iterate differs from first and its mixture");
            CHECK(message_families_normalized(graph, true),
                  "second staged round leaves every next pair normalized");
        }
    }
    g_free(raw_vf);
    g_free(raw_fv);
    g_free(first_vf);
    g_free(first_fv);
    osprey_bp_graph_free(graph);
    osprey_free(ctx);
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

static void test_fixed_convergence_boundaries(void)
{
    const double tolerance = 1e-6;
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x1c1);
    OspreyContext *ctx = new_context();
    OspreyBpGraph *graph = NULL;
    OspreyBpResult *result = NULL;
    uint32_t id = add_primitive(ctx, region, 0);
    double boundary_probability = 0.0;
    double boundary_pair[2];
    double boundary_candidate = 0.0;
    bool boundary_found = find_exact_tolerance_boundary(
        tolerance, &boundary_probability, &boundary_candidate);

    CHECK(boundary_found,
          "strict-tolerance fixture has an exactly representable delta");
    if (!boundary_found) {
        osprey_free(ctx);
        return;
    }
    add_prior(ctx, id, boundary_probability);
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "strict-tolerance boundary graph builds");
    if (graph != NULL) {
        uint32_t prior_edge = edge_for_local_rule(
            ctx, graph, local_for_offset(ctx, graph, 0), OSPREY_RULE_CA01);
        CHECK(prior_edge != UINT32_MAX,
              "strict-tolerance boundary resolves its unary edge");
        if (prior_edge != UINT32_MAX) {
            set_log_probability_pair(boundary_pair, 0.0);
            graph->msg_fv_current[(size_t)prior_edge * 2u] =
                boundary_pair[0];
            graph->msg_fv_current[(size_t)prior_edge * 2u + 1u] =
                boundary_pair[1];
            CHECK(boundary_candidate > tolerance &&
                      boundary_candidate - (boundary_candidate - tolerance) ==
                          tolerance,
                  "strict-tolerance fixture retains the exact delta");
            graph->beliefs[0] = boundary_candidate - tolerance;
            graph->beliefs[1] = boundary_candidate;
            graph->message_state = OSPREY_BP_MESSAGES_ITERATED;
            CHECK(osprey_bp_graph_validate(ctx, graph),
                  "strict-tolerance boundary state validates");
            CHECK(osprey_bp_solve_fixed(ctx, graph, &result) == OSPREY_OK &&
                      result != NULL && result->status == OSPREY_OK,
                  "delta equal to tolerance remains solvable");
            if (result != NULL) {
                CHECK(result->iterations == 11u &&
                          result->stable_rounds == 10u,
                      "delta equal to tolerance is not counted stable");
            }
        }
    }
    osprey_bp_result_free(result);
    osprey_bp_graph_free(graph);
    osprey_free(ctx);

    ctx = new_context();
    id = add_primitive(ctx, region, 8);
    add_prior(ctx, id, 1.0);
    graph = NULL;
    CHECK(osprey_bp_graph_build(ctx, &graph) == OSPREY_OK && graph != NULL,
          "stable-count reset graph builds");
    if (graph != NULL) {
        uint32_t prior_edge = edge_for_local_rule(
            ctx, graph, local_for_offset(ctx, graph, 8), OSPREY_RULE_CA01);
        CHECK(prior_edge != UINT32_MAX,
              "stable-count reset resolves its unary edge");
        if (prior_edge != UINT32_MAX) {
            set_log_probability_pair(
                &graph->msg_fv_current[(size_t)prior_edge * 2u], 0.0);
            graph->beliefs[0] = 0.5;
            graph->beliefs[1] = 0.5;
            graph->message_state = OSPREY_BP_MESSAGES_ITERATED;
            CHECK(osprey_bp_graph_validate(ctx, graph),
                  "stable-count reset state validates");
            CHECK(osprey_bp_solve_fixed(ctx, graph, &result) == OSPREY_OK &&
                      result != NULL && result->status == OSPREY_OK,
                  "stable-count reset graph converges");
            if (result != NULL) {
                CHECK(result->iterations == 29u &&
                          result->stable_rounds == 10u,
                      "an unstable round resets the ten-round stability count");
            }
        }
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
            CHECK(result->iterations == 28u && result->iterations < 500u &&
                      result->stable_rounds == 10u &&
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
            CHECK(result->iterations == 500u,
                  "nonconvergence executes round 500 rather than stopping at 499");
            CHECK(result->stable_rounds < 10u &&
                      result->nonconverged_component == 0u &&
                      isfinite(result->final_max_delta) &&
                      result->final_max_delta >= 1e-6 &&
                      isfinite(result->best_max_delta) &&
                      result->best_iteration > 0u &&
                      result->best_iteration <= 500u,
                  "nonconverged result retains deterministic diagnostics at cap");
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

static void test_generated_loopy_corpus(void)
{
    unsigned generated = 0;
    unsigned changed = 0;
    unsigned converged = 0;
    unsigned nonconverged = 0;
    unsigned max_iterations = 0;

    for (unsigned sample = 0; sample < OSPREY_BP_LOOPY_CORPUS_CASES;
         sample++) {
        OspreyContext *ctx = generated_loopy_context(sample);
        OspreyContext *permuted_ctx = NULL;
        OspreyBpGraph *graph = NULL;
        OspreyBpGraph *permuted_graph = NULL;
        OspreyBpResult *result = NULL;
        OspreyBpResult *permuted_result = NULL;
        char *graph_dump = NULL;
        char *permuted_dump = NULL;
        OspreyStatus status = OSPREY_INVALID_GRAPH;
        OspreyStatus permuted_status = OSPREY_INVALID_GRAPH;
        unsigned failed_round = UINT32_MAX;
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
                graph->components->len != 1u ||
                permuted_graph->components->len != 1u) {
                ok = false;
            }
        }
        if (ok) {
            bool trace_changed = false;
            uint64_t trace_digests[OSPREY_BP_LOOPY_TRACE_ROUNDS];
            uint64_t permuted_trace_digests[
                OSPREY_BP_LOOPY_TRACE_ROUNDS];
            bool trace_ok = run_damped_trace_pair(
                ctx, graph, permuted_ctx, permuted_graph, &trace_changed,
                trace_digests, permuted_trace_digests, &failed_round);
            if (!trace_ok || memcmp(trace_digests, permuted_trace_digests,
                                    sizeof(trace_digests)) != 0) ok = false;
            if (trace_changed) changed++;
        }
        osprey_bp_graph_free(graph);
        osprey_bp_graph_free(permuted_graph);
        graph = NULL;
        permuted_graph = NULL;
        if (ok) {
            status = osprey_bp_graph_build(ctx, &graph);
            permuted_status = osprey_bp_graph_build(
                permuted_ctx, &permuted_graph);
            if (status != OSPREY_OK || permuted_status != OSPREY_OK ||
                graph == NULL || permuted_graph == NULL) {
                ok = false;
            }
        }
        if (ok) {
            status = osprey_bp_solve_fixed(ctx, graph, &result);
            permuted_status = osprey_bp_solve_fixed(
                permuted_ctx, permuted_graph, &permuted_result);
            if (status != permuted_status ||
                (status != OSPREY_OK && status != OSPREY_NON_CONVERGED) ||
                result == NULL || permuted_result == NULL ||
                !fixed_result_metadata_equal(result, permuted_result) ||
                (status == OSPREY_OK &&
                 graph->message_state != OSPREY_BP_MESSAGES_ITERATED) ||
                (status == OSPREY_NON_CONVERGED &&
                 graph->message_state != OSPREY_BP_MESSAGES_INITIAL) ||
                !message_families_normalized(graph, false) ||
                !message_families_normalized(permuted_graph, false) ||
                !next_message_families_empty(graph) ||
                !next_message_families_empty(permuted_graph)) {
                ok = false;
            }
        }
        if (ok) {
            graph_dump = dump_graph(ctx, graph);
            permuted_dump = dump_graph(permuted_ctx, permuted_graph);
            if (graph_dump == NULL || permuted_dump == NULL ||
                strcmp(graph_dump, permuted_dump) != 0) ok = false;
        }
        if (ok) {
            if (status == OSPREY_OK) converged++;
            else nonconverged++;
            if (result->iterations > max_iterations) {
                max_iterations = result->iterations;
            }
            generated++;
        } else {
            unsigned diagnostic_round = failed_round != UINT32_MAX
                ? failed_round : result == NULL ? 0u : result->iterations;
            uint32_t component = result != NULL &&
                result->nonconverged_component != UINT32_MAX
                ? result->nonconverged_component : 0u;
            fprintf(stderr, "generated loopy mismatch at seed %u round %u "
                    "component %u status %d/%d\n", sample,
                    diagnostic_round, component, status, permuted_status);
            dump_generated_initial_state(sample, ctx, "CANONICAL");
            dump_generated_initial_state(sample, permuted_ctx, "PERMUTED");
        }
        free(graph_dump);
        free(permuted_dump);
        osprey_bp_result_free(result);
        osprey_bp_result_free(permuted_result);
        osprey_bp_graph_free(graph);
        osprey_bp_graph_free(permuted_graph);
        osprey_free(ctx);
        osprey_free(permuted_ctx);
    }
    fprintf(stderr, "loopy corpus: generated %u/%u changed %u converged %u "
            "nonconverged %u max-iterations %u\n", generated,
            OSPREY_BP_LOOPY_CORPUS_CASES, changed, converged, nonconverged,
            max_iterations);
    CHECK(generated == OSPREY_BP_LOOPY_CORPUS_CASES,
          "all generated loopy traces are deterministic and valid");
    CHECK(changed > 0,
          "generated loopy trace corpus exercises changing iterations");
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

static void test_stage54_static_closure_idempotence(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId heap = make_region(OSPREY_REGION_HEAP_SITE, 0x54);
    OspreyGraphDelta first;
    OspreyGraphDelta second;
    OspreyBpGraph *first_bp = NULL;
    OspreyBpGraph *second_bp = NULL;
    char *first_dump = NULL;
    char *second_dump = NULL;
    uint32_t primitive;

    primitive = add_primitive(ctx, heap, 32);
    set_seed(ctx, primitive, 0.6);
    OspreyMallocFact allocation;
    memset(&allocation, 0, sizeof(allocation));
    allocation.site_pc = heap.site_offset;
    allocation.requested_size = 64;
    g_array_append_val(ctx->alloc_facts, allocation);
    OspreyBaseFact base;
    memset(&base, 0, sizeof(base));
    base.chunk = make_chunk(heap, 32, 8);
    base.base = (OspreyAddress){ .region = heap, .offset = 0 };
    g_array_append_val(ctx->base_facts, base);
    CHECK(osprey_factor_add_prior(ctx, OSPREY_RULE_CA01,
                                  OSPREY_GRAPH_BASE_CA, false, 0.6,
                                  primitive).status == OSPREY_OK,
          "Stage 5.4 closure fixture prior inserted");
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "Stage 5.4 closure relations built");
    CHECK(osprey_secondary_static_closure(ctx, &first, false) == OSPREY_OK,
          "Stage 5.4 first static closure succeeds");
    CHECK(first.variables_added == 4 && first.base_factors_added == 0 &&
              first.secondary_factors_added == 7 && first.factors_added == 7 &&
              first.limit_rows_added == 0,
          "Stage 5.4 first closure reports exact graph growth");
    CHECK(osprey_bp_graph_build(ctx, &first_bp) == OSPREY_OK &&
              first_bp != NULL,
          "Stage 5.4 first closure projects");
    first_dump = dump_graph(ctx, first_bp);
    CHECK(osprey_secondary_static_closure(ctx, &second, false) == OSPREY_OK,
          "Stage 5.4 repeated static closure succeeds");
    CHECK(second.variables_added == 0 && second.base_factors_added == 0 &&
              second.secondary_factors_added == 0 && second.factors_added == 0 &&
              second.limit_rows_added == 0,
          "Stage 5.4 repeated closure has zero delta");
    CHECK(osprey_bp_graph_build(ctx, &second_bp) == OSPREY_OK &&
              second_bp != NULL,
          "Stage 5.4 repeated closure projects");
    second_dump = dump_graph(ctx, second_bp);
    CHECK(first_dump != NULL && second_dump != NULL &&
              strcmp(first_dump, second_dump) == 0,
          "Stage 5.4 repeated closure preserves canonical projection");
    free(first_dump);
    free(second_dump);
    osprey_bp_graph_free(first_bp);
    osprey_bp_graph_free(second_bp);
    osprey_free(ctx);
}

static void test_stage54_new_primitive_cascade(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId stable = make_region(OSPREY_REGION_GLOBAL, 0x54a);
    OspreyRegionId heap = make_region(OSPREY_REGION_HEAP_SITE, 0x54b);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyGraphDelta delta;
    OspreyMallocFact allocation;
    OspreyBaseFact base;
    uint32_t stable_var;
    OspreyStatus status;

    stable_var = add_primitive(ctx, stable, 0);
    set_seed(ctx, stable_var, 0.4);
    CHECK(add_prior(ctx, stable_var, 0.4),
          "Stage 5.4 primitive-cascade old factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 primitive-cascade old graph builds");
    if (old_graph != NULL) {
        uint32_t primitive = add_primitive(ctx, heap, 32);
        set_seed(ctx, primitive, 0.7);
        memset(&allocation, 0, sizeof(allocation));
        allocation.site_pc = heap.site_offset;
        allocation.requested_size = 64;
        g_array_append_val(ctx->alloc_facts, allocation);
        memset(&base, 0, sizeof(base));
        base.chunk = make_chunk(heap, 32, 8);
        base.base = (OspreyAddress){ .region = heap, .offset = 0 };
        g_array_append_val(ctx->base_facts, base);
        CHECK(osprey_relations_build(ctx) == OSPREY_OK,
              "Stage 5.4 primitive-cascade relations built");
        status = osprey_stage5_static_replay(ctx, old_graph, &delta,
                                             &new_graph);
        CHECK(status == OSPREY_OK && new_graph != NULL,
              "Stage 5.4 primitive-cascade replay succeeds");
        CHECK(delta.variables_added >= 3 && delta.secondary_factors_added >= 2 &&
                  graph_has_variable_kind(ctx, new_graph,
                                          OSPREY_PRED_UNFOLDABLE_HEAP) &&
                  graph_has_variable_kind(ctx, new_graph,
                                          OSPREY_PRED_FIELD_OF),
              "Stage 5.4 primitive growth interns CC03 and CD07 candidates");
        CHECK(graph_rule_count(ctx, new_graph, OSPREY_RULE_CC03) != 0 &&
                  graph_rule_count(ctx, new_graph, OSPREY_RULE_CD07) != 0 &&
                  graph_next_buffers_poisoned(new_graph),
              "Stage 5.4 primitive growth compiles CC03 and CD07");
        {
            OspreyBpGraph *repeat_graph = NULL;
            OspreyGraphDelta repeat_delta;
            status = osprey_stage5_static_replay(ctx, new_graph,
                                                 &repeat_delta,
                                                 &repeat_graph);
            CHECK(status == OSPREY_OK && repeat_graph == NULL &&
                      repeat_delta.variables_added == 0 &&
                      repeat_delta.factors_added == 0 &&
                      repeat_delta.limit_rows_added == 0,
                  "Stage 5.4 no-op replay keeps existing graph ownership");
            osprey_bp_graph_free(repeat_graph);
        }
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_unfoldable_prefix_closure(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId stable = make_region(OSPREY_REGION_GLOBAL, 0x54c);
    OspreyRegionId heap = make_region(OSPREY_REGION_HEAP_SITE, 0x54d);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyGraphDelta delta;
    OspreyStatus status;
    uint32_t stable_var = add_primitive(ctx, stable, 0);

    set_seed(ctx, stable_var, 0.5);
    CHECK(add_prior(ctx, stable_var, 0.5),
          "Stage 5.4 prefix-closure old factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 prefix-closure old graph builds");
    if (old_graph != NULL) {
        add_region_extent(ctx, heap, 32);
        CHECK(add_unfoldable(ctx, heap, 8) != UINT32_MAX &&
                  add_unfoldable(ctx, heap, 16) != UINT32_MAX,
              "Stage 5.4 prefix-closure candidates inserted");
        CHECK(osprey_relations_build(ctx) == OSPREY_OK,
              "Stage 5.4 prefix-closure relations built");
        status = osprey_stage5_static_replay(ctx, old_graph, &delta,
                                             &new_graph);
        CHECK(status == OSPREY_OK && new_graph != NULL,
              "Stage 5.4 prefix-closure replay succeeds");
        CHECK(graph_rule_count(ctx, new_graph, OSPREY_RULE_CC04) >= 2 &&
                  graph_rule_count(ctx, new_graph, OSPREY_RULE_CC05) >= 1,
              "Stage 5.4 prefix growth compiles CC04 and CC05");
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_post_growth_cd08(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId stable = make_region(OSPREY_REGION_GLOBAL, 0x54e);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x54f);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyGraphDelta delta;
    OspreyStatus status;
    uint32_t stable_var = add_primitive(ctx, stable, 0);

    set_seed(ctx, stable_var, 0.5);
    CHECK(add_prior(ctx, stable_var, 0.5),
          "Stage 5.4 CD08 old factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 CD08 old graph builds");
    if (old_graph != NULL) {
        add_region_extent(ctx, region, 128);
        CHECK(add_field(ctx, region, 0, 0) != UINT32_MAX &&
                  add_homo(ctx, region, 0, 100, 16) != UINT32_MAX,
              "Stage 5.4 CD08 source variables inserted");
        add_access_chunk(ctx, make_chunk(region, 100, 8));
        add_logical_access(ctx, 0x54f0, make_chunk(region, 100, 8));
        CHECK(osprey_relations_build(ctx) == OSPREY_OK,
              "Stage 5.4 CD08 relations built");
        status = osprey_stage5_static_replay(ctx, old_graph, &delta,
                                             &new_graph);
        CHECK(status == OSPREY_OK && new_graph != NULL,
              "Stage 5.4 CD08 replay succeeds");
        CHECK(graph_rule_count(ctx, new_graph, OSPREY_RULE_CD08) != 0 &&
                  graph_has_variable_kind(ctx, new_graph,
                                          OSPREY_PRED_FIELD_OF),
              "Stage 5.4 post-growth closure compiles CD08");
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_post_growth_cd04(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId stable = make_region(OSPREY_REGION_GLOBAL, 0x552);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x553);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyGraphDelta delta;
    OspreyStatus status;
    uint32_t stable_var = add_primitive(ctx, stable, 0);

    set_seed(ctx, stable_var, 0.5);
    CHECK(add_prior(ctx, stable_var, 0.5),
          "Stage 5.4 CD04 old factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 CD04 old graph builds");
    if (old_graph != NULL) {
        add_region_extent(ctx, region, 128);
        add_access_chunk(ctx, make_chunk(region, 0, 8));
        add_access_chunk(ctx, make_chunk(region, 5, 8));
        add_access_chunk(ctx, make_chunk(region, 100, 8));
        add_access_chunk(ctx, make_chunk(region, 105, 8));
        CHECK(add_homo(ctx, region, 0, 100, 10) != UINT32_MAX &&
                  add_homo(ctx, region, 5, 105, 8) != UINT32_MAX,
              "Stage 5.4 CD04 source segments inserted");
        CHECK(osprey_relations_build(ctx) == OSPREY_OK,
              "Stage 5.4 CD04 relations built");
        status = osprey_stage5_static_replay(ctx, old_graph, &delta,
                                             &new_graph);
        CHECK(status == OSPREY_OK && new_graph != NULL,
              "Stage 5.4 CD04 replay succeeds");
        CHECK(delta.variables_added >= 3 &&
                  new_graph != NULL &&
                  graph_rule_count(ctx, new_graph, OSPREY_RULE_CD04) >= 2,
              "Stage 5.4 post-growth closure compiles CD04 extensions");
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_post_growth_cd05(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId stable = make_region(OSPREY_REGION_GLOBAL, 0x550);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x551);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyGraphDelta delta;
    OspreyStatus status;
    uint32_t stable_var = add_primitive(ctx, stable, 0);

    set_seed(ctx, stable_var, 0.5);
    CHECK(add_prior(ctx, stable_var, 0.5),
          "Stage 5.4 CD05 old factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 CD05 old graph builds");
    if (old_graph != NULL) {
        uint32_t left = add_primitive(ctx, region, 4);
        uint32_t right = add_primitive_sized(ctx, region, 104, 4);
        CHECK(left != UINT32_MAX && right != UINT32_MAX &&
                  add_homo(ctx, region, 0, 100, 16) != UINT32_MAX,
              "Stage 5.4 CD05 source variables inserted");
        CHECK(osprey_relations_build(ctx) == OSPREY_OK,
              "Stage 5.4 CD05 relations built");
        status = osprey_stage5_static_replay(ctx, old_graph, &delta,
                                             &new_graph);
        CHECK(status == OSPREY_OK && new_graph != NULL,
              "Stage 5.4 CD05 replay succeeds");
        CHECK(graph_rule_count(ctx, new_graph, OSPREY_RULE_CD05) >= 2,
              "Stage 5.4 post-growth closure compiles CD05");
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_exact_resolve_coordinator(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId heap = make_region(OSPREY_REGION_HEAP_SITE, 0x541);
    OspreyChunk value = make_chunk(heap, 32, 8);
    OspreyVarPayload scalar_payload;
    OspreyInternResult scalar_result;
    OspreyVarPayload access_payload;
    OspreyInternResult access_result;
    OspreyMallocFact allocation;
    OspreyBaseFact base;
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyGraphDelta delta;
    uint32_t primitive;
    OspreyStatus status;

    primitive = add_primitive(ctx, heap, 32);
    memset(&scalar_payload, 0, sizeof(scalar_payload));
    scalar_payload.chunk = value;
    scalar_result = osprey_intern_var(ctx, OSPREY_PRED_SCALAR,
                                      &scalar_payload);
    CHECK(scalar_result.id != UINT32_MAX,
          "Stage 5.4 exact fixture scalar inserted");
    memset(&access_payload, 0, sizeof(access_payload));
    access_payload.prim_access.chunk = value;
    access_payload.prim_access.insn_pc = 0x5410;
    access_result = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_ACCESS,
                                      &access_payload);
    CHECK(access_result.id != UINT32_MAX,
          "Stage 5.4 exact fixture access inserted");
    set_seed(ctx, primitive, 0.3);
    set_seed(ctx, scalar_result.id, 0.7);
    CHECK(add_prior(ctx, primitive, 0.3) &&
              osprey_factor_add_implication(
                  ctx, OSPREY_RULE_CA06, OSPREY_GRAPH_BASE_CA, false, 0.8,
                  &access_result.id, 1, scalar_result.id).status == OSPREY_OK,
          "Stage 5.4 exact fixture base factors inserted");
    memset(&allocation, 0, sizeof(allocation));
    allocation.site_pc = heap.site_offset;
    allocation.requested_size = 64;
    g_array_append_val(ctx->alloc_facts, allocation);
    memset(&base, 0, sizeof(base));
    base.chunk = value;
    base.base = (OspreyAddress){ .region = heap, .offset = 0 };
    g_array_append_val(ctx->base_facts, base);
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "Stage 5.4 exact fixture relations built");
    status = osprey_bp_graph_build(ctx, &old_graph);
    CHECK(status == OSPREY_OK && old_graph != NULL,
          "Stage 5.4 exact old graph builds");
    if (old_graph != NULL) {
        status = osprey_stage5_static_replay(ctx, old_graph, &delta,
                                             &new_graph);
        CHECK(status == OSPREY_OK && new_graph != NULL,
              "Stage 5.4 coordinator performs static replay");
        CHECK(delta.base_factors_added != 0,
              "Stage 5.4 coordinator reports CA08 base growth");
        CHECK(new_graph != NULL && osprey_bp_graph_validate(ctx, new_graph),
              "Stage 5.4 exact replacement validates");
        if (new_graph != NULL) {
            bool exact_field = false;
            for (guint i = 0; i < ctx->graph->vars->len; i++) {
                const OspreyVar *variable = &g_array_index(
                    ctx->graph->vars, OspreyVar, i);
                if (variable->kind == OSPREY_PRED_FIELD_OF) {
                    exact_field = variable->belief_valid != 0;
                    break;
                }
            }
            CHECK(exact_field,
                  "Stage 5.4 CA08 growth reruns exact base inference");
        }
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_exact_resolve_failure_rollback(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId stable = make_region(OSPREY_REGION_GLOBAL, 0x552);
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x553);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyGraphDelta delta;
    double old_vf[2];
    double old_fv[2];
    uint32_t stable_var;
    OspreyStatus status;

    stable_var = add_primitive(ctx, stable, 0);
    set_seed(ctx, stable_var, 0.5);
    CHECK(add_prior(ctx, stable_var, 0.5),
          "Stage 5.4 exact-failure old factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 exact-failure old graph builds");
    if (old_graph != NULL) {
        memcpy(old_vf, old_graph->msg_vf_current, sizeof(old_vf));
        memcpy(old_fv, old_graph->msg_fv_current, sizeof(old_fv));
        uint32_t scalar = add_scalar(ctx, region, 0);
        uint32_t field = add_field(ctx, region, 8, 0);
        uint32_t ids[2] = { scalar, field };
        CHECK(scalar != UINT32_MAX && field != UINT32_MAX &&
                  osprey_factor_add_implication(
                      ctx, OSPREY_RULE_CA08, OSPREY_GRAPH_BASE_CA, true,
                      0.2, ids, 1, field).status == OSPREY_OK,
              "Stage 5.4 exact-failure CA08 factor inserted");
        memset(&delta, 0, sizeof(delta));
        delta.variables_added = 2;
        delta.factors_added = 1;
        delta.base_factors_added = 1;
        ctx->config.max_exact_clique_vars = 1;
        status = osprey_bp_migrate_after_delta(ctx, old_graph, &delta,
                                                &new_graph);
        CHECK(status == OSPREY_EXACT_COMPONENT_TOO_LARGE && new_graph == NULL,
              "Stage 5.4 exact re-solve failure aborts migration");
        CHECK(graph_messages_unchanged(old_graph, old_vf, old_fv),
              "Stage 5.4 exact failure preserves old messages");
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_semantic_migration(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x540);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    uint32_t first;
    uint32_t second;
    uint32_t added;
    uint64_t old_values;
    double *old_vf = NULL;
    double *old_fv = NULL;
    OspreyStatus status;

    first = add_primitive(ctx, region, 0);
    second = add_primitive(ctx, region, 8);
    set_seed(ctx, first, 0.25);
    set_seed(ctx, second, 0.75);
    CHECK(add_prior(ctx, first, 0.25) && add_prior(ctx, second, 0.75),
          "Stage 5.4 migration fixture factors inserted");
    status = osprey_bp_graph_build(ctx, &old_graph);
    CHECK(status == OSPREY_OK && old_graph != NULL,
          "Stage 5.4 old graph builds");
    if (old_graph == NULL) {
        osprey_free(ctx);
        return;
    }
    old_values = old_graph->message_values;
    old_vf = g_new(double, old_values);
    old_fv = g_new(double, old_values);
    for (uint64_t i = 0; i < old_values; i += 2) {
        double vf = ((double)i / 2.0 + 2.0) / 10.0;
        double fv = ((double)i / 2.0 + 3.0) / 11.0;
        set_log_probability_pair(&old_graph->msg_vf_current[i], vf);
        set_log_probability_pair(&old_graph->msg_fv_current[i], fv);
    }
    memcpy(old_vf, old_graph->msg_vf_current,
           old_values * sizeof(double));
    memcpy(old_fv, old_graph->msg_fv_current,
           old_values * sizeof(double));
    old_graph->message_state = OSPREY_BP_MESSAGES_ITERATED;
    for (guint local = 0; local < old_graph->vars->len; local++) {
        old_graph->beliefs[local] = 0.5;
        old_graph->beliefs[old_graph->vars->len + local] = 0.5;
    }

    added = add_primitive(ctx, region, 16);
    set_seed(ctx, added, 0.8);
    CHECK(add_prior(ctx, added, 0.8),
          "Stage 5.4 new factor inserted");
    status = osprey_bp_graph_migrate(ctx, old_graph, &new_graph);
    CHECK(status == OSPREY_OK && new_graph != NULL,
          "Stage 5.4 semantic migration succeeds");
    CHECK(new_graph != NULL && new_graph->version == old_graph->version + 1,
          "Stage 5.4 migration increments graph version");
    if (new_graph != NULL) {
        CHECK(osprey_bp_graph_validate(ctx, new_graph),
              "Stage 5.4 migrated graph validates");
        for (guint new_edge_id = 0;
             new_edge_id < new_graph->edges->len; new_edge_id++) {
            const OspreyBpEdge *new_edge = &g_array_index(
                new_graph->edges, OspreyBpEdge, new_edge_id);
            if (new_edge->graph_var_id == added) {
                const double *vf = &new_graph->msg_vf_current[
                    (size_t)new_edge_id * 2u];
                const double *fv = &new_graph->msg_fv_current[
                    (size_t)new_edge_id * 2u];
                CHECK(vf[0] == log(1.0 - 0.8) && vf[1] == log(0.8),
                      "Stage 5.4 new variable message uses base seed");
                CHECK(fv[0] == -log(2.0) && fv[1] == -log(2.0),
                      "Stage 5.4 new factor message is uniform");
            }
        }
        for (guint old_edge_id = 0;
             old_edge_id < old_graph->edges->len; old_edge_id++) {
            const OspreyBpEdge *old_edge = &g_array_index(
                old_graph->edges, OspreyBpEdge, old_edge_id);
            bool found = false;
            for (guint new_edge_id = 0;
                 new_edge_id < new_graph->edges->len; new_edge_id++) {
                const OspreyBpEdge *new_edge = &g_array_index(
                    new_graph->edges, OspreyBpEdge, new_edge_id);
                if (new_edge->graph_factor_id == old_edge->graph_factor_id &&
                    new_edge->graph_var_id == old_edge->graph_var_id &&
                    new_edge->factor_position == old_edge->factor_position) {
                    found = memcmp(&new_graph->msg_vf_current[
                                        (size_t)new_edge_id * 2u],
                                   &old_vf[(size_t)old_edge_id * 2u],
                                   2u * sizeof(double)) == 0 &&
                            memcmp(&new_graph->msg_fv_current[
                                        (size_t)new_edge_id * 2u],
                                   &old_fv[(size_t)old_edge_id * 2u],
                                   2u * sizeof(double)) == 0;
                    break;
                }
            }
            CHECK(found, "Stage 5.4 retained edge messages copied bitwise");
        }
    }
    CHECK(memcmp(old_graph->msg_vf_current, old_vf,
                 old_values * sizeof(double)) == 0 &&
              memcmp(old_graph->msg_fv_current, old_fv,
                     old_values * sizeof(double)) == 0,
          "Stage 5.4 migration leaves old ownership untouched");
    free(old_vf);
    free(old_fv);
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_migration_ignores_storage_ids(void)
{
    OspreyContext *source = new_context();
    OspreyContext *reordered = NULL;
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x546);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    uint32_t first = add_primitive(source, region, 0);
    uint32_t second = add_primitive(source, region, 8);

    set_seed(source, first, 0.2);
    set_seed(source, second, 0.8);
    CHECK(add_prior(source, first, 0.2) && add_prior(source, second, 0.8),
          "Stage 5.4 storage-ID fixture factors inserted");
    CHECK(osprey_bp_graph_build(source, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 storage-ID old graph builds");
    reordered = reverse_clone_context(source);
    CHECK(reordered != NULL,
          "Stage 5.4 storage-ID reordered source builds");
    if (old_graph != NULL && reordered != NULL) {
        for (guint edge_id = 0; edge_id < old_graph->edges->len; edge_id++) {
            size_t index = (size_t)edge_id * 2u;
            set_log_probability_pair(&old_graph->msg_vf_current[index],
                                     0.3 + 0.1 * edge_id);
            set_log_probability_pair(&old_graph->msg_fv_current[index],
                                     0.4 + 0.1 * edge_id);
        }
        old_graph->message_state = OSPREY_BP_MESSAGES_ITERATED;
        for (guint local = 0; local < old_graph->vars->len; local++) {
            old_graph->beliefs[local] = 0.5;
            old_graph->beliefs[old_graph->vars->len + local] = 0.5;
        }
        uint32_t added = add_primitive(reordered, region, 16);
        set_seed(reordered, added, 0.6);
        CHECK(add_prior(reordered, added, 0.6),
              "Stage 5.4 storage-ID growth inserted");
        CHECK(osprey_bp_graph_migrate(reordered, old_graph, &new_graph) ==
                  OSPREY_OK && new_graph != NULL,
              "Stage 5.4 migration accepts reordered storage IDs");
        if (new_graph != NULL) {
            for (guint old_id = 0; old_id < old_graph->edges->len; old_id++) {
                const OspreyBpEdge *old_edge = &g_array_index(
                    old_graph->edges, OspreyBpEdge, old_id);
                bool found = false;
                for (guint new_id = 0; new_id < new_graph->edges->len;
                     new_id++) {
                    const OspreyBpEdge *new_edge = &g_array_index(
                        new_graph->edges, OspreyBpEdge, new_id);
                    if (old_edge->factor_position ==
                            new_edge->factor_position &&
                        osprey_factor_key_equal(&old_edge->key.factor,
                                                &new_edge->key.factor) &&
                        osprey_key_equal(&old_edge->key.variable,
                                         &new_edge->key.variable)) {
                        found = memcmp(&old_graph->msg_vf_current[
                                           (size_t)old_id * 2u],
                                       &new_graph->msg_vf_current[
                                           (size_t)new_id * 2u],
                                       2u * sizeof(double)) == 0 &&
                                memcmp(&old_graph->msg_fv_current[
                                           (size_t)old_id * 2u],
                                       &new_graph->msg_fv_current[
                                           (size_t)new_id * 2u],
                                       2u * sizeof(double)) == 0;
                        break;
                    }
                }
                CHECK(found,
                      "Stage 5.4 storage-ID migration preserves semantic edge");
            }
        }
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(reordered);
    osprey_free(source);
}

typedef struct Stage54ReferenceFactorKey {
    uint16_t rule;
    uint8_t stage;
    uint8_t potential_kind;
    uint8_t negative;
    uint8_t reserved;
    uint16_t head_idx;
    uint16_t reserved2;
    uint64_t p_bits;
    uint32_t num_vars;
    OspreyKey var_keys[OSPREY_FACTOR_MAX_ARITY];
} Stage54ReferenceFactorKey;

typedef struct Stage54ReferenceEdgeKey {
    Stage54ReferenceFactorKey factor;
    uint32_t factor_position;
    OspreyKey variable;
} Stage54ReferenceEdgeKey;

typedef struct Stage54ReferenceMigrationEntry {
    Stage54ReferenceEdgeKey key;
    uint32_t edge_id;
    uint8_t consumed;
    uint8_t reserved[3];
} Stage54ReferenceMigrationEntry;

static bool stage54_size_add(uint64_t *total, uint64_t count, size_t size)
{
    uint64_t bytes;
    if (total == NULL || (count != 0 && size > UINT64_MAX / count)) {
        return false;
    }
    bytes = count * size;
    if (*total > UINT64_MAX - bytes) return false;
    *total += bytes;
    return true;
}

static bool stage54_reference_graph_workspace(const OspreyBpGraph *graph,
                                              uint64_t *out)
{
    uint64_t total = sizeof(OspreyBpGraph) + 4u * sizeof(GArray) +
                     sizeof(GPtrArray);
    if (graph == NULL || out == NULL || graph->vars == NULL ||
        graph->factors == NULL || graph->edges == NULL ||
        graph->var_edges == NULL || graph->components == NULL ||
        !stage54_size_add(&total, graph->vars->len,
                          sizeof(OspreyBpVarRef)) ||
        !stage54_size_add(&total, graph->factors->len,
                          sizeof(OspreyBpFactorRef)) ||
        !stage54_size_add(&total, graph->edges->len,
                          sizeof(OspreyBpEdge)) ||
        !stage54_size_add(&total, graph->var_edges->len,
                          sizeof(uint32_t)) ||
        !stage54_size_add(&total, graph->vars->len, sizeof(uint32_t)) ||
        !stage54_size_add(&total, graph->factors->len, sizeof(uint32_t)) ||
        !stage54_size_add(&total, graph->components->len, sizeof(gpointer)) ||
        !stage54_size_add(&total, graph->message_values, 5u * sizeof(double)) ||
        !stage54_size_add(&total, (uint64_t)graph->vars->len * 2u,
                          sizeof(double))) {
        return false;
    }
    for (guint i = 0; i < graph->components->len; i++) {
        const OspreyBpComponent *component = g_ptr_array_index(
            graph->components, i);
        if (component == NULL || component->local_vars == NULL ||
            component->local_factors == NULL || component->edges == NULL ||
            !stage54_size_add(&total, 1, sizeof(OspreyBpComponent)) ||
            !stage54_size_add(&total, 3, sizeof(GArray)) ||
            !stage54_size_add(&total, component->local_vars->len,
                              sizeof(uint32_t)) ||
            !stage54_size_add(&total, component->local_factors->len,
                              sizeof(uint32_t)) ||
            !stage54_size_add(&total, component->edges->len,
                              sizeof(uint32_t))) {
            return false;
        }
    }
    *out = total;
    return true;
}

static bool stage54_reference_migration_peak(const OspreyBpGraph *old_graph,
                                             const OspreyBpGraph *new_graph,
                                             uint64_t *out)
{
    uint64_t old_workspace;
    uint64_t new_workspace;
    uint64_t total = 0;
    if (!stage54_reference_graph_workspace(old_graph, &old_workspace) ||
        !stage54_reference_graph_workspace(new_graph, &new_workspace) ||
        !stage54_size_add(&total, 1, old_workspace) ||
        !stage54_size_add(&total, 1, new_workspace) ||
        !stage54_size_add(&total, old_graph->edges->len,
                          sizeof(Stage54ReferenceMigrationEntry)) ||
        !stage54_size_add(&total, new_graph->edges->len,
                          sizeof(Stage54ReferenceEdgeKey)) ||
        !stage54_size_add(&total, new_graph->edges->len, sizeof(uint8_t)) ||
        !stage54_size_add(&total, new_graph->vars->len, sizeof(OspreyKey)) ||
        !stage54_size_add(&total, new_graph->factors->len,
                          sizeof(Stage54ReferenceFactorKey)) ||
        !stage54_size_add(&total, new_graph->edges->len,
                          sizeof(Stage54ReferenceEdgeKey))) {
        return false;
    }
    *out = total;
    return true;
}

typedef struct Stage54SemanticEdge {
    uint16_t rule;
    uint16_t head_idx;
    uint8_t stage;
    uint8_t potential_kind;
    uint8_t negative;
    uint64_t p_bits;
    uint32_t num_vars;
    uint32_t factor_position;
    OspreyKey factor_variables[OSPREY_FACTOR_MAX_ARITY];
    OspreyKey variable;
} Stage54SemanticEdge;

static bool stage54_semantic_edge_capture(const OspreyContext *ctx,
                                          const OspreyBpGraph *graph,
                                          uint32_t edge_id,
                                          Stage54SemanticEdge *out)
{
    const OspreyBpEdge *edge;
    uint32_t factor_id;
    const OspreyFactor *factor;
    if (ctx == NULL || ctx->graph == NULL || graph == NULL || out == NULL ||
        graph->edges == NULL || edge_id >= graph->edges->len) return false;
    edge = &g_array_index(graph->edges, OspreyBpEdge, edge_id);
    factor_id = edge_graph_factor_id(graph, edge_id);
    if (factor_id >= ctx->graph->factors->len ||
        edge->graph_var_id >= ctx->graph->vars->len) return false;
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, factor_id);
    if (factor == NULL || factor->num_vars == 0 ||
        factor->num_vars > OSPREY_FACTOR_MAX_ARITY ||
        factor->var_ids == NULL || edge->factor_position >= factor->num_vars) {
        return false;
    }
    memset(out, 0, sizeof(*out));
    out->rule = factor->rule;
    out->head_idx = factor->head_idx;
    out->stage = factor->stage;
    out->potential_kind = factor->potential_kind;
    out->negative = factor->negative;
    memcpy(&out->p_bits, &factor->p, sizeof(out->p_bits));
    out->num_vars = factor->num_vars;
    out->factor_position = edge->factor_position;
    for (uint32_t position = 0; position < factor->num_vars; position++) {
        uint32_t graph_var_id = factor->var_ids[position];
        if (graph_var_id >= ctx->graph->vars->len) return false;
        const OspreyVar *variable = &g_array_index(
            ctx->graph->vars, OspreyVar, graph_var_id);
        out->factor_variables[position] = osprey_var_key(
            variable->kind, &variable->payload);
    }
    {
        const OspreyVar *variable = &g_array_index(
            ctx->graph->vars, OspreyVar, edge->graph_var_id);
        out->variable = osprey_var_key(variable->kind, &variable->payload);
    }
    return true;
}

static bool stage54_semantic_edge_equal(const Stage54SemanticEdge *left,
                                        const Stage54SemanticEdge *right)
{
    if (left == NULL || right == NULL || left->rule != right->rule ||
        left->head_idx != right->head_idx || left->stage != right->stage ||
        left->potential_kind != right->potential_kind ||
        left->negative != right->negative || left->p_bits != right->p_bits ||
        left->num_vars != right->num_vars ||
        left->factor_position != right->factor_position ||
        !osprey_key_equal(&left->variable, &right->variable)) {
        return false;
    }
    for (uint32_t i = 0; i < left->num_vars; i++) {
        if (!osprey_key_equal(&left->factor_variables[i],
                              &right->factor_variables[i])) return false;
    }
    return true;
}

static double stage54_migration_probability(uint32_t sample,
                                            uint32_t index,
                                            uint32_t salt)
{
    return 0.1 + (double)((sample * 37u + index * 17u + salt * 13u) % 75u) /
        100.0;
}

static uint32_t stage54_migration_rng(uint32_t *state)
{
    *state = *state * 1664525u + 1013904223u;
    return *state;
}

static const uint8_t stage54_pair_endpoints[8][2] = {
    { 0, 1 }, { 1, 2 }, { 0, 2 }, { 2, 3 },
    { 1, 3 }, { 0, 3 }, { 3, 4 }, { 2, 4 },
};

static OspreyContext *stage54_migration_context(uint32_t variable_count,
                                                 uint32_t secondary_mask,
                                                 uint32_t sample,
                                                 bool reverse)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL,
                                        0x560000u + sample);
    uint32_t graph_ids[6];
    uint32_t factor_count = variable_count + 8;

    if (ctx == NULL || variable_count < 2 || variable_count > 6) {
        osprey_free(ctx);
        return NULL;
    }
    for (uint32_t position = 0; position < variable_count; position++) {
        uint32_t semantic = reverse ? variable_count - position - 1 : position;
        OspreyVarPayload payload;
        OspreyInternResult result;
        memset(&payload, 0, sizeof(payload));
        payload.chunk = make_chunk(region, (int64_t)semantic * 16, 8);
        result = osprey_intern_var(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                   &payload);
        if (result.id == UINT32_MAX) {
            osprey_free(ctx);
            return NULL;
        }
        graph_ids[semantic] = result.id;
        set_seed(ctx, result.id,
                 stage54_migration_probability(sample, semantic, 1));
    }
    for (uint32_t position = 0; position < factor_count; position++) {
        uint32_t factor_index = reverse ? factor_count - position - 1 : position;
        OspreyFactorResult result;
        if (factor_index < variable_count) {
            uint32_t semantic = factor_index;
            result = osprey_factor_add_prior(
                ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, false,
                stage54_migration_probability(sample, semantic, 1),
                graph_ids[semantic]);
        } else {
            uint32_t pair = factor_index - variable_count;
            if ((secondary_mask & (1u << pair)) == 0) continue;
            uint32_t antecedent = graph_ids[stage54_pair_endpoints[pair][0]];
            uint32_t head = graph_ids[stage54_pair_endpoints[pair][1]];
            uint16_t rule = (uint16_t)(OSPREY_RULE_CB01 + pair);
            result = osprey_factor_add_implication(
                ctx, rule, OSPREY_GRAPH_SECONDARY,
                (sample & (1u << pair)) != 0,
                stage54_migration_probability(sample, pair, 9),
                &antecedent, 1, head);
        }
        if (result.status != OSPREY_OK) {
            osprey_free(ctx);
            return NULL;
        }
    }
    return ctx;
}

static bool stage54_migration_oracle_case(uint32_t sample)
{
    OspreyContext *old_ctx = NULL;
    OspreyContext *new_ctx = NULL;
    OspreyContext *permuted_ctx = NULL;
    OspreyContext *failure_ctx = NULL;
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *reference_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyBpGraph *permuted_graph = NULL;
    Stage54SemanticEdge *old_edges = NULL;
    bool *old_used = NULL;
    double *old_vf = NULL;
    double *old_fv = NULL;
    char *new_dump = NULL;
    char *permuted_dump = NULL;
    uint32_t rng = sample ^ 0x54a5e5u;
    uint32_t old_count = 2 + stage54_migration_rng(&rng) % 3;
    uint32_t new_count = old_count + stage54_migration_rng(&rng) % 3;
    uint32_t old_valid = 0;
    uint32_t new_valid = 0;
    uint32_t old_secondary;
    uint32_t new_secondary;
    uint64_t old_workspace;
    uint64_t new_workspace;
    uint64_t migration_peak;
    bool ok = false;

    for (uint32_t pair = 0; pair < 8; pair++) {
        if (stage54_pair_endpoints[pair][0] < old_count &&
            stage54_pair_endpoints[pair][1] < old_count) {
            old_valid |= 1u << pair;
        }
        if (stage54_pair_endpoints[pair][0] < new_count &&
            stage54_pair_endpoints[pair][1] < new_count) {
            new_valid |= 1u << pair;
        }
    }
    old_secondary = stage54_migration_rng(&rng) & old_valid;
    new_secondary = (old_secondary & stage54_migration_rng(&rng)) |
                    (stage54_migration_rng(&rng) & new_valid);
    old_ctx = stage54_migration_context(old_count, old_secondary, sample,
                                        false);
    new_ctx = stage54_migration_context(new_count, new_secondary, sample,
                                        false);
    permuted_ctx = stage54_migration_context(new_count, new_secondary, sample,
                                             true);
    failure_ctx = stage54_migration_context(new_count, new_secondary, sample,
                                            false);
    if (old_ctx == NULL || new_ctx == NULL || permuted_ctx == NULL ||
        failure_ctx == NULL ||
        osprey_bp_graph_build(old_ctx, &old_graph) != OSPREY_OK ||
        old_graph == NULL ||
        osprey_bp_graph_build(new_ctx, &reference_graph) != OSPREY_OK ||
        reference_graph == NULL ||
        !stage54_reference_graph_workspace(old_graph, &old_workspace) ||
        !stage54_reference_graph_workspace(reference_graph, &new_workspace) ||
        old_workspace != old_graph->workspace_bytes ||
        new_workspace != reference_graph->workspace_bytes ||
        !stage54_reference_migration_peak(old_graph, reference_graph,
                                          &migration_peak) ||
        migration_peak == 0) goto out;
    osprey_bp_graph_free(reference_graph);
    reference_graph = NULL;
    for (guint edge_id = 0; edge_id < old_graph->edges->len; edge_id++) {
        size_t index = (size_t)edge_id * 2u;
        set_log_probability_pair(
            &old_graph->msg_vf_current[index],
            0.12 + (double)((sample + edge_id * 7u) % 70u) / 100.0);
        set_log_probability_pair(
            &old_graph->msg_fv_current[index],
            0.18 + (double)((sample + edge_id * 11u) % 65u) / 100.0);
    }
    old_graph->message_state = OSPREY_BP_MESSAGES_ITERATED;
    for (guint local = 0; local < old_graph->vars->len; local++) {
        old_graph->beliefs[local] = 0.5;
        old_graph->beliefs[old_graph->vars->len + local] = 0.5;
    }
    old_vf = g_new(double, old_graph->message_values);
    old_fv = g_new(double, old_graph->message_values);
    memcpy(old_vf, old_graph->msg_vf_current,
           (size_t)old_graph->message_values * sizeof(double));
    memcpy(old_fv, old_graph->msg_fv_current,
           (size_t)old_graph->message_values * sizeof(double));
    old_edges = g_new0(Stage54SemanticEdge, old_graph->edges->len);
    old_used = g_new0(bool, old_graph->edges->len);
    for (guint edge_id = 0; edge_id < old_graph->edges->len; edge_id++) {
        if (!stage54_semantic_edge_capture(old_ctx, old_graph, edge_id,
                                           &old_edges[edge_id])) goto out;
    }
    if (migration_peak == 0) goto out;
    failure_ctx->config.max_bp_table_bytes = migration_peak - 1u;
    old_graph->workspace_limit = migration_peak - 1u;
    {
        OspreyBpGraph *failed_graph = NULL;
        OspreyStatus failed_status = osprey_bp_graph_migrate(
            failure_ctx, old_graph, &failed_graph);
        osprey_bp_graph_free(failed_graph);
        if (failed_status != OSPREY_LIMIT_EXCEEDED || failed_graph != NULL ||
            !graph_messages_unchanged(old_graph, old_vf, old_fv)) goto out;
    }
    new_ctx->config.max_bp_table_bytes = migration_peak;
    permuted_ctx->config.max_bp_table_bytes = migration_peak;
    old_graph->workspace_limit = migration_peak;
    if (osprey_bp_graph_migrate(new_ctx, old_graph, &new_graph) !=
            OSPREY_OK ||
        new_graph == NULL || !osprey_bp_graph_validate(new_ctx, new_graph) ||
        new_graph->workspace_bytes != new_workspace ||
        new_graph->workspace_limit != migration_peak ||
        new_graph->message_state != OSPREY_BP_MESSAGES_ITERATED ||
        !graph_next_buffers_poisoned(new_graph)) goto out;
    {
        uint32_t matched = 0;
        for (guint new_id = 0; new_id < new_graph->edges->len; new_id++) {
            Stage54SemanticEdge new_edge;
            uint32_t match = UINT32_MAX;
            if (!stage54_semantic_edge_capture(new_ctx, new_graph, new_id,
                                               &new_edge)) goto out;
            for (guint prior = 0; prior < new_id; prior++) {
                Stage54SemanticEdge prior_edge;
                if (!stage54_semantic_edge_capture(new_ctx, new_graph, prior,
                                                   &prior_edge)) goto out;
                if (stage54_semantic_edge_equal(&new_edge, &prior_edge)) {
                    goto out;
                }
            }
            for (guint old_id = 0; old_id < old_graph->edges->len; old_id++) {
                if (old_used[old_id] ||
                    !stage54_semantic_edge_equal(&new_edge,
                                                 &old_edges[old_id])) continue;
                match = old_id;
                break;
            }
            if (match != UINT32_MAX) {
                old_used[match] = true;
                matched++;
                if (memcmp(&new_graph->msg_vf_current[(size_t)new_id * 2u],
                           &old_vf[(size_t)match * 2u],
                           2u * sizeof(double)) != 0 ||
                    memcmp(&new_graph->msg_fv_current[(size_t)new_id * 2u],
                           &old_fv[(size_t)match * 2u],
                           2u * sizeof(double)) != 0) goto out;
            } else {
                bool old_variable = false;
                for (guint old_id = 0; old_id < old_graph->edges->len;
                     old_id++) {
                    if (osprey_key_equal(&new_edge.variable,
                                         &old_edges[old_id].variable)) {
                        old_variable = true;
                        break;
                    }
                }
                const double *vf = &new_graph->msg_vf_current[
                    (size_t)new_id * 2u];
                const double *fv = &new_graph->msg_fv_current[
                    (size_t)new_id * 2u];
                if (fv[0] != -log(2.0) || fv[1] != -log(2.0)) goto out;
                if (old_variable) {
                    if (vf[0] != -log(2.0) || vf[1] != -log(2.0)) {
                        goto out;
                    }
                } else {
                    const OspreyBpEdge *edge = &g_array_index(
                        new_graph->edges, OspreyBpEdge, new_id);
                    const OspreyBpVarRef *variable = &g_array_index(
                        new_graph->vars, OspreyBpVarRef, edge->local_var);
                    double expected_vf[2];
                    expected_vf[0] = variable->base_seed[0] == 0.0
                        ? -INFINITY : log(variable->base_seed[0]);
                    expected_vf[1] = variable->base_seed[1] == 0.0
                        ? -INFINITY : log(variable->base_seed[1]);
                    if (!variable->base_seed_valid ||
                        memcmp(vf, expected_vf,
                               2u * sizeof(double)) != 0) goto out;
                }
            }
        }
        bool changed = old_graph->vars->len != new_graph->vars->len ||
                       old_graph->factors->len != new_graph->factors->len ||
                       old_graph->edges->len != new_graph->edges->len ||
                       matched != old_graph->edges->len;
        if (new_graph->version != old_graph->version + (changed ? 1u : 0u)) {
            goto out;
        }
    }
    if (!graph_messages_unchanged(old_graph, old_vf, old_fv)) goto out;
    new_dump = dump_graph(new_ctx, new_graph);
    if (new_dump == NULL ||
        osprey_bp_graph_migrate(permuted_ctx, old_graph, &permuted_graph) !=
            OSPREY_OK ||
        permuted_graph == NULL ||
        !osprey_bp_graph_validate(permuted_ctx, permuted_graph)) goto out;
    permuted_dump = dump_graph(permuted_ctx, permuted_graph);
    if (permuted_dump == NULL || strcmp(new_dump, permuted_dump) != 0 ||
        !graph_messages_unchanged(old_graph, old_vf, old_fv)) goto out;
    ok = true;
out:
    if (!ok) {
        fprintf(stderr, "Stage 5.4 migration oracle mismatch at sample %u\n",
                sample);
        dump_generated_round_failure(sample, old_ctx, old_graph);
        dump_generated_round_failure(sample, new_ctx, new_graph);
        dump_generated_round_failure(sample, permuted_ctx, permuted_graph);
        dump_generated_round_failure(sample, failure_ctx, NULL);
    }
    free(new_dump);
    free(permuted_dump);
    g_free(old_edges);
    g_free(old_used);
    g_free(old_vf);
    g_free(old_fv);
    osprey_bp_graph_free(permuted_graph);
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(reference_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(failure_ctx);
    osprey_free(permuted_ctx);
    osprey_free(new_ctx);
    osprey_free(old_ctx);
    return ok;
}

static void test_stage54_migration_oracle(void)
{
    unsigned generated = 0;
    for (unsigned sample = 0; sample < 2000; sample++) {
        if (!stage54_migration_oracle_case(sample)) break;
        generated++;
    }
    CHECK(generated == 2000,
          "Stage 5.4 semantic migration matches the 2000-case oracle");
}

static void test_stage54_source_shrink_migration(void)
{
    OspreyContext *old_ctx = stage54_migration_context(4, 0x07, 0x5a0,
                                                       false);
    OspreyContext *new_ctx = stage54_migration_context(2, 0, 0x5a0, true);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    Stage54SemanticEdge *old_edges = NULL;
    double *old_vf = NULL;
    double *old_fv = NULL;
    OspreyStatus status;

    CHECK(old_ctx != NULL && new_ctx != NULL &&
              osprey_bp_graph_build(old_ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 source-shrink old graph builds");
    if (old_graph != NULL && new_ctx != NULL) {
        old_edges = g_new0(Stage54SemanticEdge, old_graph->edges->len);
        old_vf = g_new(double, old_graph->message_values);
        old_fv = g_new(double, old_graph->message_values);
        old_graph->message_state = OSPREY_BP_MESSAGES_ITERATED;
        for (guint edge_id = 0; edge_id < old_graph->edges->len; edge_id++) {
            size_t index = (size_t)edge_id * 2u;
            set_log_probability_pair(&old_graph->msg_vf_current[index],
                                     0.21 + 0.03 * edge_id);
            set_log_probability_pair(&old_graph->msg_fv_current[index],
                                     0.31 + 0.02 * edge_id);
            CHECK(stage54_semantic_edge_capture(old_ctx, old_graph, edge_id,
                                                 &old_edges[edge_id]),
                  "Stage 5.4 source-shrink captures old semantic edge");
        }
        memcpy(old_vf, old_graph->msg_vf_current,
               (size_t)old_graph->message_values * sizeof(double));
        memcpy(old_fv, old_graph->msg_fv_current,
               (size_t)old_graph->message_values * sizeof(double));
        for (guint local = 0; local < old_graph->vars->len; local++) {
            old_graph->beliefs[local] = 0.5;
            old_graph->beliefs[old_graph->vars->len + local] = 0.5;
        }
        status = osprey_bp_graph_migrate(new_ctx, old_graph, &new_graph);
        CHECK(status == OSPREY_OK && new_graph != NULL &&
                  new_graph->vars->len == 2 &&
                  osprey_bp_graph_validate(new_ctx, new_graph),
              "Stage 5.4 source-shrink migration validates");
        if (new_graph != NULL) {
            for (guint new_id = 0; new_id < new_graph->edges->len; new_id++) {
                Stage54SemanticEdge new_edge;
                bool retained = false;
                CHECK(stage54_semantic_edge_capture(new_ctx, new_graph,
                                                     new_id, &new_edge),
                      "Stage 5.4 source-shrink captures new semantic edge");
                for (guint old_id = 0; old_id < old_graph->edges->len;
                     old_id++) {
                    if (!stage54_semantic_edge_equal(&new_edge,
                                                     &old_edges[old_id])) {
                        continue;
                    }
                    retained = memcmp(&new_graph->msg_vf_current[
                                           (size_t)new_id * 2u],
                                      &old_vf[(size_t)old_id * 2u],
                                      2u * sizeof(double)) == 0 &&
                               memcmp(&new_graph->msg_fv_current[
                                           (size_t)new_id * 2u],
                                      &old_fv[(size_t)old_id * 2u],
                                      2u * sizeof(double)) == 0;
                    break;
                }
                CHECK(retained,
                      "Stage 5.4 source-shrink preserves retained messages");
            }
        }
    }
    g_free(old_edges);
    g_free(old_vf);
    g_free(old_fv);
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(new_ctx);
    osprey_free(old_ctx);
}

static bool stage54_try_migration_limit(OspreyContext *ctx,
                                        OspreyBpGraph *old_graph,
                                        uint64_t limit,
                                        OspreyStatus *status_out)
{
    OspreyBpGraph *replacement = NULL;
    OspreyStatus status;
    if (ctx == NULL || old_graph == NULL) return false;
    ctx->config.max_bp_table_bytes = limit;
    old_graph->workspace_limit = limit;
    status = osprey_bp_graph_migrate(ctx, old_graph, &replacement);
    if (status_out != NULL) *status_out = status;
    osprey_bp_graph_free(replacement);
    return status == OSPREY_OK;
}

static void stage54_mutate_factor_during_migration(OspreyContext *ctx)
{
    OspreyFactor *factor;
    if (ctx == NULL || ctx->graph == NULL || ctx->graph->factors->len == 0) {
        return;
    }
    factor = g_array_index(ctx->graph->factors, OspreyFactor *, 0);
    if (factor != NULL) factor->p = 0.61;
}

static void stage54_mutate_limit_during_migration(OspreyContext *ctx)
{
    if (ctx != NULL && ctx->graph != NULL &&
        ctx->graph->limit_rows != UINT64_MAX) {
        ctx->graph->limit_rows++;
    }
}

static OspreyBpGraph *stage54_old_graph_hook;

static void stage54_duplicate_old_edge_during_migration(OspreyContext *ctx)
{
    (void)ctx;
    if (stage54_old_graph_hook == NULL ||
        stage54_old_graph_hook->edges == NULL ||
        stage54_old_graph_hook->edges->len < 2) return;
    OspreyBpEdge *first = &g_array_index(stage54_old_graph_hook->edges,
                                         OspreyBpEdge, 0);
    OspreyBpEdge *second = &g_array_index(stage54_old_graph_hook->edges,
                                          OspreyBpEdge, 1);
    second->key = first->key;
}

static bool stage54_message_case(unsigned family, unsigned corruption,
                                 bool hard_true)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL,
                                        0x554 + family * 16 + corruption);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    Stage54SemanticEdge old_edge;
    uint32_t first = add_primitive(ctx, region, 0);
    bool ok = false;

    set_seed(ctx, first, 0.4);
    if (!add_prior(ctx, first, 0.4) ||
        osprey_bp_graph_build(ctx, &old_graph) != OSPREY_OK ||
        old_graph == NULL ||
        !stage54_semantic_edge_capture(ctx, old_graph, 0, &old_edge)) {
        goto out;
    }
    old_graph->message_state = OSPREY_BP_MESSAGES_ITERATED;
    old_graph->beliefs[0] = 0.5;
    old_graph->beliefs[1] = 0.5;
    uint32_t added = add_primitive(ctx, region, 8);
    set_seed(ctx, added, 0.6);
    if (!add_prior(ctx, added, 0.6)) goto out;
    double *pair = family == 0 ? old_graph->msg_vf_current
                               : old_graph->msg_fv_current;
    if (corruption == UINT32_MAX) {
        pair[hard_true ? 0 : 1] = -INFINITY;
        pair[hard_true ? 1 : 0] = 0.0;
        if (osprey_bp_graph_migrate(ctx, old_graph, &new_graph) != OSPREY_OK ||
            new_graph == NULL) goto out;
        for (guint edge_id = 0; edge_id < new_graph->edges->len; edge_id++) {
            Stage54SemanticEdge candidate;
            if (!stage54_semantic_edge_capture(ctx, new_graph, edge_id,
                                               &candidate)) goto out;
            if (!stage54_semantic_edge_equal(&old_edge, &candidate)) continue;
            const double *migrated = family == 0
                ? &new_graph->msg_vf_current[(size_t)edge_id * 2u]
                : &new_graph->msg_fv_current[(size_t)edge_id * 2u];
            ok = memcmp(migrated, pair, 2u * sizeof(double)) == 0;
            goto out;
        }
    } else {
        switch (corruption) {
        case 0:
            pair[0] = NAN;
            break;
        case 1:
            pair[0] = INFINITY;
            break;
        case 2:
            pair[0] = -INFINITY;
            pair[1] = -INFINITY;
            break;
        case 3:
            pair[0] = 0.0;
            pair[1] = 0.0;
            break;
        default:
            goto out;
        }
        ok = osprey_bp_graph_migrate(ctx, old_graph, &new_graph) ==
                 OSPREY_INVALID_GRAPH && new_graph == NULL;
    }
out:
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
    return ok;
}

static void test_stage54_rejects_corrupt_messages(void)
{
    bool corruptions_reject = true;
    bool hard_zero_preserved = true;
    for (unsigned family = 0; family < 2; family++) {
        for (unsigned corruption = 0; corruption < 4; corruption++) {
            corruptions_reject = stage54_message_case(
                family, corruption, false) && corruptions_reject;
        }
        hard_zero_preserved =
            stage54_message_case(family, UINT32_MAX, false) &&
            stage54_message_case(family, UINT32_MAX, true) &&
            hard_zero_preserved;
    }
    CHECK(corruptions_reject,
          "Stage 5.4 rejects the complete current-message corruption matrix");
    CHECK(hard_zero_preserved,
          "Stage 5.4 preserves exact hard-zero current messages");
}

static void test_stage54_rejects_duplicate_semantics(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x555);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyStatus status;
    uint32_t id = add_primitive(ctx, region, 0);

    set_seed(ctx, id, 0.5);
    CHECK(add_prior(ctx, id, 0.5),
          "Stage 5.4 duplicate-semantic factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 duplicate-semantic old graph builds");
    if (old_graph != NULL) {
        const OspreyFactor *original = g_array_index(
            ctx->graph->factors, OspreyFactor *, 0);
        OspreyFactor *duplicate = g_new0(OspreyFactor, 1);
        *duplicate = *original;
        duplicate->id = ctx->graph->factors->len;
        duplicate->var_ids = g_new(uint32_t, original->num_vars);
        memcpy(duplicate->var_ids, original->var_ids,
               (size_t)original->num_vars * sizeof(uint32_t));
        g_array_append_val(ctx->graph->factors, duplicate);
        status = osprey_bp_graph_migrate(ctx, old_graph, &new_graph);
        CHECK(status == OSPREY_INVALID_GRAPH && new_graph == NULL,
              "Stage 5.4 rejects duplicate semantic factor identity");
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_rejects_duplicate_old_edges(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x5551);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    uint32_t first = add_primitive(ctx, region, 0);
    uint32_t second = add_primitive(ctx, region, 8);

    set_seed(ctx, first, 0.4);
    set_seed(ctx, second, 0.6);
    CHECK(add_prior(ctx, first, 0.4) && add_prior(ctx, second, 0.6),
          "Stage 5.4 duplicate-old-edge factors inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL && old_graph->edges->len >= 2,
          "Stage 5.4 duplicate-old-edge graph builds");
    if (old_graph != NULL && old_graph->edges->len >= 2) {
        uint32_t added = add_primitive(ctx, region, 16);
        set_seed(ctx, added, 0.5);
        CHECK(add_prior(ctx, added, 0.5),
              "Stage 5.4 duplicate-old-edge growth inserted");
        stage54_old_graph_hook = old_graph;
        osprey_bp_test_set_migration_hook(
            stage54_duplicate_old_edge_during_migration);
        CHECK(osprey_bp_graph_migrate(ctx, old_graph, &new_graph) ==
                  OSPREY_INVALID_GRAPH && new_graph == NULL,
              "Stage 5.4 old semantic-edge index rejects duplicates");
        osprey_bp_test_set_migration_hook(NULL);
        stage54_old_graph_hook = NULL;
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_stale_fingerprint_rollback(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x556);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    double old_vf[2];
    double old_fv[2];
    OspreyFactor *factor;
    OspreyStatus status;
    uint32_t id = add_primitive(ctx, region, 0);

    set_seed(ctx, id, 0.4);
    CHECK(add_prior(ctx, id, 0.4),
          "Stage 5.4 fingerprint factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 fingerprint old graph builds");
    if (old_graph != NULL) {
        uint32_t added = add_primitive(ctx, region, 8);
        set_seed(ctx, added, 0.6);
        CHECK(add_prior(ctx, added, 0.6),
              "Stage 5.4 fingerprint growth inserted");
        memcpy(old_vf, old_graph->msg_vf_current, sizeof(old_vf));
        memcpy(old_fv, old_graph->msg_fv_current, sizeof(old_fv));
        factor = g_array_index(ctx->graph->factors, OspreyFactor *, 0);
        osprey_bp_test_set_migration_hook(
            stage54_mutate_factor_during_migration);
        status = osprey_bp_graph_migrate(ctx, old_graph, &new_graph);
        osprey_bp_test_set_migration_hook(NULL);
        CHECK(status == OSPREY_INVALID_GRAPH && new_graph == NULL,
              "Stage 5.4 rejects a stale source fingerprint");
        CHECK(graph_messages_unchanged(old_graph, old_vf, old_fv),
              "Stage 5.4 fingerprint rejection preserves old messages");
        factor->p = 0.4;
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_stale_limit_fingerprint_rollback(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x557);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyStatus status;
    uint64_t original_limit_rows;
    uint32_t first = add_primitive(ctx, region, 0);

    set_seed(ctx, first, 0.4);
    CHECK(add_prior(ctx, first, 0.4),
          "Stage 5.4 limit-fingerprint factor inserted");
    original_limit_rows = ctx->graph->limit_rows;
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 limit-fingerprint old graph builds");
    if (old_graph != NULL) {
        uint32_t added = add_primitive(ctx, region, 8);
        set_seed(ctx, added, 0.6);
        CHECK(add_prior(ctx, added, 0.6),
              "Stage 5.4 limit-fingerprint growth inserted");
        osprey_bp_test_set_migration_hook(
            stage54_mutate_limit_during_migration);
        status = osprey_bp_graph_migrate(ctx, old_graph, &new_graph);
        osprey_bp_test_set_migration_hook(NULL);
        CHECK(status == OSPREY_INVALID_GRAPH && new_graph == NULL,
              "Stage 5.4 rejects a stale limit-row fingerprint");
        ctx->graph->limit_rows = original_limit_rows;
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_allocation_failure_rollback(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x557);
    OspreyBpGraph *old_graph = NULL;
    double *old_vf = NULL;
    double *old_fv = NULL;
    OspreyStatus status = OSPREY_OK;
    bool all_failures_clean = true;
    bool success = false;
    uint32_t first = add_primitive(ctx, region, 0);

    set_seed(ctx, first, 0.3);
    CHECK(add_prior(ctx, first, 0.3),
          "Stage 5.4 allocation-failure old factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 allocation-failure old graph builds");
    if (old_graph != NULL) {
        uint32_t added = add_primitive(ctx, region, 8);
        set_seed(ctx, added, 0.7);
        CHECK(add_secondary(ctx, OSPREY_RULE_CB02, &first, 1, added),
              "Stage 5.4 allocation-failure growth inserted");
        old_vf = g_new(double, old_graph->message_values);
        old_fv = g_new(double, old_graph->message_values);
        memcpy(old_vf, old_graph->msg_vf_current,
               (size_t)old_graph->message_values * sizeof(double));
        memcpy(old_fv, old_graph->msg_fv_current,
               (size_t)old_graph->message_values * sizeof(double));
        for (int64_t fail_after = 0; fail_after < 512 && !success;
             fail_after++) {
            OspreyBpGraph *replacement = NULL;
            osprey_bp_test_set_alloc_fail_after(fail_after);
            status = osprey_bp_graph_migrate(ctx, old_graph, &replacement);
            osprey_bp_test_set_alloc_fail_after(-1);
            if (status == OSPREY_OK && replacement != NULL) {
                success = true;
            } else {
                if (status != OSPREY_INVALID_GRAPH || replacement != NULL ||
                    !graph_messages_unchanged(old_graph, old_vf, old_fv)) {
                    all_failures_clean = false;
                }
            }
            osprey_bp_graph_free(replacement);
        }
        CHECK(all_failures_clean && success,
              "Stage 5.4 allocation failures roll back until success");
    }
    osprey_bp_test_set_alloc_fail_after(-1);
    g_free(old_vf);
    g_free(old_fv);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_workspace_boundary(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x558);
    OspreyBpGraph *old_graph = NULL;
    OspreyStatus status = OSPREY_OK;
    uint64_t high = 1;
    uint64_t low;
    uint32_t first = add_primitive(ctx, region, 0);

    set_seed(ctx, first, 0.4);
    CHECK(add_prior(ctx, first, 0.4),
          "Stage 5.4 workspace-boundary old factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 workspace-boundary old graph builds");
    if (old_graph != NULL) {
        uint32_t added = add_primitive(ctx, region, 8);
        set_seed(ctx, added, 0.6);
        CHECK(add_prior(ctx, added, 0.6),
              "Stage 5.4 workspace-boundary growth inserted");
        while (high < (1ULL << 32) &&
               !stage54_try_migration_limit(ctx, old_graph, high, &status)) {
            high <<= 1;
        }
        if (high >= (1ULL << 32) &&
            !stage54_try_migration_limit(ctx, old_graph, high, &status)) {
            CHECK(false, "Stage 5.4 workspace boundary has an accepting limit");
        } else {
            low = 0;
            while (low < high) {
                uint64_t middle = low + (high - low) / 2;
                if (stage54_try_migration_limit(ctx, old_graph, middle,
                                                &status)) {
                    high = middle;
                } else {
                    low = middle + 1;
                }
            }
            CHECK(stage54_try_migration_limit(ctx, old_graph, low, &status),
                  "Stage 5.4 exact concurrent workspace limit accepts");
            if (low != 0) {
                bool accepted = stage54_try_migration_limit(
                    ctx, old_graph, low - 1, &status);
                CHECK(!accepted && status == OSPREY_LIMIT_EXCEEDED,
                      "Stage 5.4 one-byte workspace deficit rejects");
            }
        }
    }
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_version_overflow_rollback(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x559);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyStatus status;
    uint32_t first = add_primitive(ctx, region, 0);

    set_seed(ctx, first, 0.5);
    CHECK(add_prior(ctx, first, 0.5),
          "Stage 5.4 version-overflow old factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 version-overflow old graph builds");
    if (old_graph != NULL) {
        uint32_t added = add_primitive(ctx, region, 8);
        set_seed(ctx, added, 0.5);
        CHECK(add_prior(ctx, added, 0.5),
              "Stage 5.4 version-overflow growth inserted");
        old_graph->version = UINT64_MAX;
        status = osprey_bp_graph_migrate(ctx, old_graph, &new_graph);
        CHECK(status == OSPREY_LIMIT_EXCEEDED && new_graph == NULL,
              "Stage 5.4 rejects graph-version overflow");
        CHECK(old_graph->version == UINT64_MAX,
              "Stage 5.4 version overflow preserves old graph");
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_explicit_growth_coordinator(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x543);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyGraphDelta delta;
    uint32_t first;
    uint32_t second;

    first = add_primitive(ctx, region, 0);
    set_seed(ctx, first, 0.3);
    CHECK(add_prior(ctx, first, 0.3),
          "Stage 5.4 explicit-growth old factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 explicit-growth old graph builds");
    if (old_graph != NULL) {
        second = add_primitive(ctx, region, 8);
        set_seed(ctx, second, 0.7);
        CHECK(add_secondary(ctx, OSPREY_RULE_CB02, &first, 1, second),
              "Stage 5.4 explicit-growth new factor inserted");
        CHECK(osprey_relations_build(ctx) == OSPREY_OK,
              "Stage 5.4 explicit-growth relations built");
        CHECK(osprey_stage5_static_replay(ctx, old_graph, &delta,
                                          &new_graph) == OSPREY_OK &&
                  new_graph != NULL,
              "Stage 5.4 coordinator migrates explicit growth");
        CHECK(delta.variables_added == 1 && delta.factors_added == 1 &&
                  delta.base_factors_added == 0 &&
                  delta.secondary_factors_added == 1,
              "Stage 5.4 coordinator counts explicit secondary growth");
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_initial_growth_preserves_seed_beliefs(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x544);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    uint32_t first = add_primitive(ctx, region, 0);
    uint32_t second = add_primitive(ctx, region, 8);
    uint32_t added;

    set_seed(ctx, first, 0.25);
    set_seed(ctx, second, 0.75);
    CHECK(add_prior(ctx, first, 0.25) && add_prior(ctx, second, 0.75),
          "Stage 5.4 initial-belief fixture factors inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 initial-belief old graph builds");
    if (old_graph != NULL) {
        added = add_primitive(ctx, region, 16);
        CHECK(add_secondary(ctx, OSPREY_RULE_CB02, &first, 1, added),
              "Stage 5.4 initial-belief growth inserted");
        CHECK(osprey_bp_graph_migrate(ctx, old_graph, &new_graph) ==
                  OSPREY_OK && new_graph != NULL,
              "Stage 5.4 initial-belief migration succeeds");
        if (new_graph != NULL) {
            uint32_t first_local = local_for_offset(ctx, new_graph, 0);
            uint32_t second_local = local_for_offset(ctx, new_graph, 8);
            uint32_t added_local = local_for_offset(ctx, new_graph, 16);
            CHECK(new_graph->message_state == OSPREY_BP_MESSAGES_ITERATED &&
                      first_local != UINT32_MAX &&
                      second_local != UINT32_MAX &&
                      added_local != UINT32_MAX,
                  "Stage 5.4 grown initial graph has complete belief state");
            if (first_local != UINT32_MAX && second_local != UINT32_MAX &&
                added_local != UINT32_MAX) {
                CHECK(new_graph->beliefs[first_local] == 0.25 &&
                          new_graph->beliefs[new_graph->vars->len +
                                             first_local] == 0.25 &&
                          new_graph->beliefs[second_local] == 0.75 &&
                          new_graph->beliefs[new_graph->vars->len +
                                             second_local] == 0.75 &&
                          new_graph->beliefs[added_local] == 0.5 &&
                          new_graph->beliefs[new_graph->vars->len +
                                             added_local] == 0.5,
                      "Stage 5.4 growth preserves exact initial beliefs");
            }
        }
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_rejects_inconsistent_delta(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x545);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyGraphDelta delta;
    uint32_t first = add_primitive(ctx, region, 0);

    set_seed(ctx, first, 0.4);
    CHECK(add_prior(ctx, first, 0.4),
          "Stage 5.4 delta fixture old factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 delta fixture old graph builds");
    if (old_graph != NULL) {
        uint32_t added = add_primitive(ctx, region, 8);
        double old_vf[2];
        double old_fv[2];
        set_seed(ctx, added, 0.6);
        CHECK(add_prior(ctx, added, 0.6),
              "Stage 5.4 delta fixture new base factor inserted");
        memcpy(old_vf, old_graph->msg_vf_current, sizeof(old_vf));
        memcpy(old_fv, old_graph->msg_fv_current, sizeof(old_fv));
        memset(&delta, 0, sizeof(delta));
        delta.variables_added = 1;
        delta.factors_added = 1;
        delta.secondary_factors_added = 1;
        CHECK(osprey_bp_migrate_after_delta(ctx, old_graph, &delta,
                                             &new_graph) ==
                  OSPREY_INVALID_GRAPH && new_graph == NULL,
              "Stage 5.4 rejects a misclassified base-factor delta");
        CHECK(memcmp(old_graph->msg_vf_current, old_vf, sizeof(old_vf)) == 0 &&
                  memcmp(old_graph->msg_fv_current, old_fv,
                         sizeof(old_fv)) == 0,
              "Stage 5.4 delta rejection preserves old messages");
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_rejects_limit_only_delta(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x5451);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    OspreyGraphDelta delta;
    double old_vf[2];
    double old_fv[2];
    uint32_t first = add_primitive(ctx, region, 0);

    set_seed(ctx, first, 0.4);
    CHECK(add_prior(ctx, first, 0.4),
          "Stage 5.4 limit-only fixture factor inserted");
    CHECK(osprey_relations_build(ctx) == OSPREY_OK,
          "Stage 5.4 limit-only fixture relations built");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 limit-only old graph builds");
    if (old_graph != NULL) {
        memcpy(old_vf, old_graph->msg_vf_current, sizeof(old_vf));
        memcpy(old_fv, old_graph->msg_fv_current, sizeof(old_fv));
        ctx->graph->limit_rows++;
        CHECK(osprey_stage5_static_replay(ctx, old_graph, &delta,
                                          &new_graph) ==
                  OSPREY_LIMIT_EXCEEDED && new_graph == NULL,
              "Stage 5.4 rejects limit-only graph growth");
        CHECK(delta.variables_added == 0 && delta.factors_added == 0 &&
                  delta.limit_rows_added == 1,
              "Stage 5.4 reports the complete limit-only delta");
        CHECK(osprey_bp_graph_migrate(ctx, old_graph, &new_graph) ==
                  OSPREY_LIMIT_EXCEEDED && new_graph == NULL,
              "Stage 5.4 direct migration rejects source limit growth");
        CHECK(memcmp(old_graph->msg_vf_current, old_vf, sizeof(old_vf)) == 0 &&
                  memcmp(old_graph->msg_fv_current, old_fv,
                         sizeof(old_fv)) == 0,
              "Stage 5.4 limit-only rejection preserves old messages");
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_workspace_rejects_before_allocation(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x547);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *sized_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    uint32_t first = add_primitive(ctx, region, 0);

    set_seed(ctx, first, 0.4);
    CHECK(add_prior(ctx, first, 0.4),
          "Stage 5.4 workspace fixture old factor inserted");
    CHECK(osprey_bp_graph_build(ctx, &old_graph) == OSPREY_OK &&
              old_graph != NULL,
          "Stage 5.4 workspace old graph builds");
    if (old_graph != NULL) {
        uint32_t added = add_primitive(ctx, region, 8);
        set_seed(ctx, added, 0.6);
        CHECK(add_prior(ctx, added, 0.6),
              "Stage 5.4 workspace fixture growth inserted");
        CHECK(osprey_bp_graph_build(ctx, &sized_graph) == OSPREY_OK &&
                  sized_graph != NULL,
              "Stage 5.4 workspace replacement size is known");
        if (sized_graph != NULL) {
            uint64_t limit = old_graph->workspace_bytes +
                             sized_graph->workspace_bytes - 1u;
            CHECK(limit > old_graph->workspace_bytes &&
                      limit > sized_graph->workspace_bytes,
                  "Stage 5.4 workspace limit fits each graph separately");
            ctx->config.max_bp_table_bytes = limit;
            old_graph->workspace_limit = limit;
            osprey_bp_test_set_alloc_fail_after(0);
            CHECK(osprey_bp_graph_migrate(ctx, old_graph, &new_graph) ==
                      OSPREY_LIMIT_EXCEEDED && new_graph == NULL,
                  "Stage 5.4 peak limit rejects before fingerprint allocation");
            osprey_bp_test_set_alloc_fail_after(-1);
        }
    }
    osprey_bp_test_set_alloc_fail_after(-1);
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(sized_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_changed_factor_is_new_edge(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x542);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    uint32_t id = add_primitive(ctx, region, 0);
    OspreyStatus status;

    set_seed(ctx, id, 0.4);
    CHECK(add_prior(ctx, id, 0.4),
          "Stage 5.4 changed-factor fixture inserted");
    status = osprey_bp_graph_build(ctx, &old_graph);
    CHECK(status == OSPREY_OK && old_graph != NULL,
          "Stage 5.4 changed-factor old graph builds");
    if (old_graph != NULL) {
        old_graph->message_state = OSPREY_BP_MESSAGES_ITERATED;
        old_graph->beliefs[0] = 0.4;
        old_graph->beliefs[1] = 0.4;
        g_array_index(ctx->graph->factors, OspreyFactor *, 0)->p = 0.6;
        status = osprey_bp_graph_migrate(ctx, old_graph, &new_graph);
        CHECK(status == OSPREY_OK && new_graph != NULL,
              "Stage 5.4 changed factor migrates");
        if (new_graph != NULL) {
            CHECK(new_graph->version == 1 &&
                      new_graph->msg_vf_current[0] == -log(2.0) &&
                      new_graph->msg_vf_current[1] == -log(2.0),
                  "Stage 5.4 changed factor initializes a new edge");
        }
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

static void test_stage54_changed_role_is_new_edge(void)
{
    OspreyContext *ctx = new_context();
    OspreyRegionId region = make_region(OSPREY_REGION_GLOBAL, 0x5421);
    OspreyBpGraph *old_graph = NULL;
    OspreyBpGraph *new_graph = NULL;
    uint32_t first = add_primitive(ctx, region, 0);
    uint32_t second = add_primitive(ctx, region, 8);
    OspreyStatus status;

    set_seed(ctx, first, 0.4);
    set_seed(ctx, second, 0.6);
    CHECK(add_secondary(ctx, OSPREY_RULE_CB02, &first, 1, second),
          "Stage 5.4 changed-role factor inserted");
    status = osprey_bp_graph_build(ctx, &old_graph);
    CHECK(status == OSPREY_OK && old_graph != NULL,
          "Stage 5.4 changed-role old graph builds");
    if (old_graph != NULL) {
        OspreyFactor *factor = g_array_index(
            ctx->graph->factors, OspreyFactor *, 0);
        old_graph->message_state = OSPREY_BP_MESSAGES_ITERATED;
        for (guint edge_id = 0; edge_id < old_graph->edges->len; edge_id++) {
            size_t index = (size_t)edge_id * 2u;
            set_log_probability_pair(&old_graph->msg_vf_current[index],
                                     0.2 + 0.1 * edge_id);
            set_log_probability_pair(&old_graph->msg_fv_current[index],
                                     0.3 + 0.1 * edge_id);
        }
        for (guint local = 0; local < old_graph->vars->len; local++) {
            old_graph->beliefs[local] = 0.5;
            old_graph->beliefs[old_graph->vars->len + local] = 0.5;
        }
        CHECK(factor != NULL && factor->num_vars == 2,
              "Stage 5.4 changed-role source factor is binary");
        if (factor != NULL && factor->num_vars == 2) {
            uint32_t swap = factor->var_ids[0];
            factor->var_ids[0] = factor->var_ids[1];
            factor->var_ids[1] = swap;
            status = osprey_bp_graph_migrate(ctx, old_graph, &new_graph);
            CHECK(status == OSPREY_OK && new_graph != NULL,
                  "Stage 5.4 changed semantic role migrates");
            if (new_graph != NULL) {
                bool all_uniform = true;
                for (uint64_t i = 0; i < new_graph->message_values; i++) {
                    if (new_graph->msg_vf_current[i] != -log(2.0) ||
                        new_graph->msg_fv_current[i] != -log(2.0)) {
                        all_uniform = false;
                        break;
                    }
                }
                CHECK(new_graph->version == old_graph->version + 1 &&
                          all_uniform,
                      "Stage 5.4 changed roles initialize only new edges");
            }
        }
    }
    osprey_bp_graph_free(new_graph);
    osprey_bp_graph_free(old_graph);
    osprey_free(ctx);
}

int main(void)
{
    RUN(test_stage54_static_closure_idempotence);
    RUN(test_stage54_new_primitive_cascade);
    RUN(test_stage54_unfoldable_prefix_closure);
    RUN(test_stage54_post_growth_cd08);
    RUN(test_stage54_post_growth_cd04);
    RUN(test_stage54_post_growth_cd05);
    RUN(test_stage54_explicit_growth_coordinator);
    RUN(test_stage54_initial_growth_preserves_seed_beliefs);
    RUN(test_stage54_rejects_inconsistent_delta);
    RUN(test_stage54_rejects_limit_only_delta);
    RUN(test_stage54_workspace_rejects_before_allocation);
    RUN(test_stage54_changed_factor_is_new_edge);
    RUN(test_stage54_changed_role_is_new_edge);
    RUN(test_stage54_exact_resolve_coordinator);
    RUN(test_stage54_exact_resolve_failure_rollback);
    RUN(test_stage54_semantic_migration);
    RUN(test_stage54_migration_ignores_storage_ids);
    RUN(test_stage54_migration_oracle);
    RUN(test_stage54_source_shrink_migration);
    RUN(test_stage54_rejects_corrupt_messages);
    RUN(test_stage54_rejects_duplicate_semantics);
    RUN(test_stage54_rejects_duplicate_old_edges);
    RUN(test_stage54_stale_fingerprint_rollback);
    RUN(test_stage54_stale_limit_fingerprint_rollback);
    RUN(test_stage54_allocation_failure_rollback);
    RUN(test_stage54_workspace_boundary);
    RUN(test_stage54_version_overflow_rollback);
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
    RUN(test_fixed_round_damping);
    RUN(test_fixed_graph_solver);
    RUN(test_fixed_solver_failures);
    RUN(test_fixed_workspace_failure);
    RUN(test_fixed_message_failure_matrix);
    RUN(test_fixed_convergence_boundaries);
    RUN(test_fixed_convergence_policy);
    RUN(test_fixed_horn_support);
    RUN(test_fixed_real_nonconvergence);
    RUN(test_generated_fixed_forests);
    RUN(test_generated_loopy_corpus);
    RUN(test_generated_projections);

    if (failures != 0 || executed != registered) {
        fprintf(stderr, "FAIL stage5_bp (%u failures, %u/%u)\n",
                failures, executed, registered);
        return 1;
    }
    printf("PASS stage5_bp (%u/%u; fixed forests 2000/2000; "
           "loopy %u/%u; projections 2000/2000)\n", executed, registered,
           OSPREY_BP_LOOPY_CORPUS_CASES, OSPREY_BP_LOOPY_CORPUS_CASES);
    return 0;
}
