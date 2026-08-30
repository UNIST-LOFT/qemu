/*
 * OSPREY deterministic closure (R01-R12), predicate interning, bounded
 * candidate generation, and static factor instantiation (Stage 3).
 *
 * Parent side only: runs after the baseline sample is merged.  This
 * stage delivers the abstract predicates and rule-instance factors the
 * inference stage solves; nothing here computes marginals.
 *
 * Rule semantics follow the corrected reference
 * (agent-docs/info/OSPREY_TYPE_INFERENCE/OSPREY_IMPLEMENTATION.md §4-§7):
 *  - R01-R09 deterministic aggregations over committed facts;
 *  - R10-R12 hint instances (DataFlow / UnifiedAccess / PointsTo);
 *  - CD04 closure extends HomoSegment candidates from hints;
 *  - factor convention (§7.1): compile A--p-->B as one factor that
 *    penalizes only the violated assignment by 1-p; split X<->Y into
 *    two directional factors; split multi-head consequents per head;
 *    p_k = min(1, distinct_sample_paths / total_sampled_paths) (§7.2);
 *    p_s = p_up; hint-instance counts remain diagnostics only.
 *
 * Candidate discipline (§9):
 *  - addresses only from observed chunks, BaseAddr bases, region bases,
 *    heap bases, or rule endpoints;
 *  - arrays only from CB01-CB05 or canonical intervals, half-open hi,
 *    stride > 0, hi > lo, hi-lo >= s;
 *  - homo segments only from R10-R12 and CD04 closure, capped to
 *    observed region extent, starts aligned to observed chunk starts;
 *  - per-(kind,region) caps from config, with [osprey] [limit] rows.
 *
 * Determinism: all iterations are over insertion-ordered committed
 * GArrays (parent side), so the graph construction is reproducible.
 */

#include "osprey.h"
#include "osprey-internal.h"

/* Diagnostic sink (snapshot.c). */
void log_msg(const char *fmt, ...);

/* ------------------------------------------------------------------ */
/* Small helpers (H01-H06)                                             */
/* ------------------------------------------------------------------ */

static bool same_region(const OspreyRegionId *a, const OspreyRegionId *b) {
    return a->kind == b->kind && a->code_image_id == b->code_image_id &&
           a->site_offset == b->site_offset;
}

static bool same_region_addr(const OspreyAddress *a, const OspreyAddress *b) {
    return same_region(&a->region, &b->region);
}

/* H02: offset difference a-b; false when regions differ or overflow. */
static bool offset_between(const OspreyAddress *a, const OspreyAddress *b,
                           int64_t *out) {
    if (!same_region_addr(a, b)) return false;
    return osprey_check_sub(a->offset, b->offset, out);
}

static bool address_equal(const OspreyAddress *a, const OspreyAddress *b) {
    return same_region_addr(a, b) && a->offset == b->offset;
}

static bool chunk_equal(const OspreyChunk *a, const OspreyChunk *b) {
    return address_equal(&a->address, &b->address) && a->size == b->size;
}

/* p_k per §7.2: distinct supporting samples over total sampled paths. */
static bool support_ratio(OspreyContext *ctx, uint32_t sample_support,
                          double *out)
{
    if (ctx == NULL || out == NULL || ctx->total_samples == 0) {
        return false;
    }
    double ratio = (double)sample_support / (double)ctx->total_samples;
    if (ratio > 1.0) ratio = 1.0;
    *out = ratio;
    return true;
}

/* ------------------------------------------------------------------ */
/* R10-R12 hint extraction                                             */
/* ------------------------------------------------------------------ */

static void hint_add(OspreyContext *ctx, OspreyAddress a1, OspreyAddress a2,
                     int64_t s, uint8_t kind, uint64_t instances) {
    OspreyGraph *g = ctx->graph;
    for (guint i = 0; i < g->hints->len; i++) {
        OspreyHint *e = &g_array_index(g->hints, OspreyHint, i);
        if (e->kind == kind && e->size == s &&
            address_equal(&e->a1, &a1) && address_equal(&e->a2, &a2)) {
            if (UINT64_MAX - e->instances < instances) {
                e->instances = UINT64_MAX;
            } else {
                e->instances += instances;
            }
            if (UINT64_MAX - g->hint_instances < instances) {
                g->hint_instances = UINT64_MAX;
            } else {
                g->hint_instances += instances;
            }
            return;
        }
    }
    OspreyHint h;
    memset(&h, 0, sizeof(h));
    h.a1 = a1;
    h.a2 = a2;
    h.size = s;
    h.kind = kind;
    h.instances = instances;
    g_array_append_val(g->hints, h);
    if (UINT64_MAX - g->hint_instances < instances) {
        g->hint_instances = UINT64_MAX;
    } else {
        g->hint_instances += instances;
    }
}

/* R10-R12 are materialized by osprey-relations.c.  The graph stage only
 * transfers those immutable hint rows; it must not reconstruct them from
 * class-specific F01 rows or from insertion order. */
static void closure_r10(OspreyContext *ctx) {
    if (ctx->relations == NULL) return;
    for (guint i = 0; i < ctx->relations->r10_data_flow->len; i++) {
        const OspreyHintRelation *r = &g_array_index(
            ctx->relations->r10_data_flow, OspreyHintRelation, i);
        hint_add(ctx, r->a1, r->a2, r->size,
                 OSPREY_RELATION_DATA_FLOW, r->witness_count);
    }
}

static void closure_r11(OspreyContext *ctx) {
    if (ctx->relations == NULL) return;
    for (guint i = 0; i < ctx->relations->r11_unified_access->len; i++) {
        const OspreyHintRelation *r = &g_array_index(
            ctx->relations->r11_unified_access, OspreyHintRelation, i);
        hint_add(ctx, r->a1, r->a2, r->size,
                 OSPREY_RELATION_UNIFIED_ACCESS, r->witness_count);
    }
}

static void closure_r12(OspreyContext *ctx) {
    if (ctx->relations == NULL) return;
    for (guint i = 0; i < ctx->relations->r12_points_to->len; i++) {
        const OspreyHintRelation *r = &g_array_index(
            ctx->relations->r12_points_to, OspreyHintRelation, i);
        hint_add(ctx, r->a1, r->a2, r->size,
                 OSPREY_RELATION_POINTS_TO, r->witness_count);
    }
}

/* ------------------------------------------------------------------ */
/* Static factor instantiation (CA/CB/CC/CD base rules)                */
/* ------------------------------------------------------------------ */

#define P_UP 0.8
#define P_DN 0.2

static OspreyStatus rules_error(OspreyContext *ctx, OspreyStatus status)
{
    if (ctx != NULL && (ctx->last_status == OSPREY_OK ||
                        ctx->last_status == OSPREY_DISABLED)) {
        ctx->last_status = status;
    }
    return status;
}

static uint32_t rule_var_id(OspreyContext *ctx, uint8_t kind,
                            const OspreyVarPayload *payload)
{
    if (ctx == NULL || ctx->graph == NULL || payload == NULL) return UINT32_MAX;
    OspreyKey key = osprey_var_key(kind, payload);
    gpointer value = g_hash_table_lookup(ctx->graph->var_index, &key);
    return value == NULL ? UINT32_MAX : (uint32_t)(uintptr_t)value - 1;
}

static const OspreyLogicalAccess *logical_access_find(
    const OspreyRelations *relations, uint64_t pc, const OspreyChunk *chunk)
{
    if (relations == NULL || chunk == NULL) return NULL;
    for (guint i = 0; i < relations->logical_accesses->len; i++) {
        const OspreyLogicalAccess *row = &g_array_index(
            relations->logical_accesses, OspreyLogicalAccess, i);
        if (row->pc == pc && chunk_equal(&row->chunk, chunk)) return row;
    }
    return NULL;
}

static bool logical_group_contains(const OspreyRelations *relations,
                                   uint64_t pc,
                                   const OspreyRegionId *region,
                                   bool multi)
{
    if (relations == NULL || region == NULL) return false;
    const GArray *groups = multi ? relations->r04_multi_chunk
                                 : relations->r03_single_chunk;
    for (guint i = 0; i < groups->len; i++) {
        const OspreyInsnRegionRelation *row = &g_array_index(
            groups, OspreyInsnRegionRelation, i);
        if (row->pc == pc && same_region(&row->region, region)) return true;
    }
    return false;
}

static const OspreyInsnRegionAddressRelation *relation_extreme_find(
    const GArray *rows, uint64_t pc, const OspreyRegionId *region)
{
    if (rows == NULL || region == NULL) return NULL;
    for (guint i = 0; i < rows->len; i++) {
        const OspreyInsnRegionAddressRelation *row = &g_array_index(
            rows, OspreyInsnRegionAddressRelation, i);
        if (row->pc == pc && same_region(&row->region, region)) return row;
    }
    return NULL;
}

static void candidate_append(GArray *proposals, uint8_t kind,
                             const OspreyVarPayload *payload,
                             uint64_t direct_support, double prior,
                             uint16_t source_rule)
{
    OspreyCandidateProposal proposal;
    memset(&proposal, 0, sizeof(proposal));
    proposal.predicate_kind = kind;
    proposal.payload = *payload;
    proposal.direct_support = direct_support;
    proposal.prior = prior;
    proposal.source_rule = source_rule;
    g_array_append_val(proposals, proposal);
}

/* Replay must not add the same deterministic evidence to an already
 * interned candidate.  Keep all proposals for a candidate that is new at the
 * start of this batch so candidate_select can merge independent witnesses;
 * discard only proposals whose semantic key is already resident. */
static OspreyStatus select_new_candidates(OspreyContext *ctx,
                                          const GArray *proposals)
{
    GArray *fresh;
    OspreyStatus status;

    if (ctx == NULL || ctx->graph == NULL || proposals == NULL) {
        return rules_error(ctx, OSPREY_INVALID_GRAPH);
    }
    fresh = g_array_new(FALSE, FALSE, sizeof(OspreyCandidateProposal));
    for (guint i = 0; i < proposals->len; i++) {
        const OspreyCandidateProposal *proposal = &g_array_index(
            proposals, OspreyCandidateProposal, i);
        OspreyKey key = osprey_var_key(proposal->predicate_kind,
                                       &proposal->payload);
        if (g_hash_table_lookup(ctx->graph->var_index, &key) == NULL) {
            g_array_append_val(fresh, *proposal);
        }
    }
    status = fresh->len == 0 ? OSPREY_OK : osprey_candidate_select(
        ctx, (const OspreyCandidateProposal *)fresh->data, fresh->len);
    g_array_free(fresh, TRUE);
    return status;
}

static bool array_payload_make(const OspreyAddress *lo,
                               const OspreyAddress *hi, int64_t stride,
                               OspreyVarPayload *payload)
{
    int64_t span;
    if (lo == NULL || hi == NULL || payload == NULL || stride <= 0 ||
        !same_region_addr(lo, hi) || lo->offset >= hi->offset ||
        !osprey_check_sub(hi->offset, lo->offset, &span) ||
        span < stride) {
        return false;
    }
    memset(payload, 0, sizeof(*payload));
    payload->segment.a1 = *lo;
    payload->segment.a2 = *hi;
    payload->segment.size = stride;
    return true;
}

static bool support_for_logical(OspreyContext *ctx,
                                const OspreyLogicalAccess *row,
                                double *out)
{
    return row != NULL && support_ratio(ctx, row->sample_support, out);
}

/* CA01 candidates and factors are driven by the parent-local logical
 * Access projection.  F01 class and direction are deliberately absent. */
static OspreyStatus collect_ca01(OspreyContext *ctx, GArray *proposals)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < relations->logical_accesses->len; i++) {
        const OspreyLogicalAccess *row = &g_array_index(
            relations->logical_accesses, OspreyLogicalAccess, i);
        double pk;
        if (!support_for_logical(ctx, row, &pk)) {
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        OspreyVarPayload payload;
        memset(&payload, 0, sizeof(payload));
        payload.chunk = row->chunk;
        candidate_append(proposals, OSPREY_PRED_PRIMITIVE_VAR, &payload,
                         row->sample_support, pk, OSPREY_RULE_CA01);
    }
    return OSPREY_OK;
}

static OspreyStatus compile_ca01(OspreyContext *ctx)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < relations->logical_accesses->len; i++) {
        const OspreyLogicalAccess *row = &g_array_index(
            relations->logical_accesses, OspreyLogicalAccess, i);
        OspreyVarPayload payload;
        memset(&payload, 0, sizeof(payload));
        payload.chunk = row->chunk;
        uint32_t id = rule_var_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &payload);
        if (id == UINT32_MAX) continue;
        double pk;
        if (!support_for_logical(ctx, row, &pk)) {
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        {
            OspreyFactorResult result = osprey_factor_add_prior(
                ctx, OSPREY_RULE_CA01, OSPREY_GRAPH_BASE_CA, false, pk, id);
            if (result.status != OSPREY_OK) return result.status;
        }
    }
    return OSPREY_OK;
}

/* CA02/CA03: every complete-width pair in R02 contributes at most one
 * canonical bidirectional rule instance.  The relation helpers keep the
 * direction of H03/H04 separate from predicate-key canonicalization. */
static OspreyStatus compile_ca02_ca03(OspreyContext *ctx)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < relations->r02_accessed->len; i++) {
        const OspreyChunkRelation *left = &g_array_index(
            relations->r02_accessed, OspreyChunkRelation, i);
        for (guint j = i + 1; j < relations->r02_accessed->len; j++) {
            const OspreyChunkRelation *right = &g_array_index(
                relations->r02_accessed, OspreyChunkRelation, j);
            const OspreyChunk *a = &left->chunk;
            const OspreyChunk *b = &right->chunk;
            bool adjacent = osprey_relation_adjacent_chunk(a, b);
            bool overlap = osprey_relation_overlapping_chunk(a, b) ||
                           osprey_relation_overlapping_chunk(b, a);
            if (!adjacent && !overlap) continue;

            OspreyVarPayload pa, pb;
            memset(&pa, 0, sizeof(pa));
            memset(&pb, 0, sizeof(pb));
            pa.chunk = *a;
            pb.chunk = *b;
            uint32_t va = rule_var_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pa);
            uint32_t vb = rule_var_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pb);
            if (va == UINT32_MAX || vb == UINT32_MAX) continue;
            OspreyFactorBatchResult batch;
            if (adjacent) {
                batch = osprey_factor_add_bidirectional(
                    ctx, OSPREY_RULE_CA02, OSPREY_GRAPH_BASE_CA, false,
                    P_UP, va, vb);
                if (batch.status != OSPREY_OK) return batch.status;
            }
            if (overlap) {
                batch = osprey_factor_add_bidirectional(
                    ctx, OSPREY_RULE_CA03, OSPREY_GRAPH_BASE_CA, true,
                    P_DN, va, vb);
                if (batch.status != OSPREY_OK) return batch.status;
            }
        }
    }
    return OSPREY_OK;
}

/* CA04/CA05: concrete PrimitiveAccess variables retain semantic order.
 * CA05 is the complete same-instruction P02 x R01 join, including chunks in
 * different regions. */
static OspreyStatus collect_ca04_ca05(OspreyContext *ctx, GArray *proposals)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < relations->r01_accessed->len; i++) {
        const OspreyInsnChunkRelation *row = &g_array_index(
            relations->r01_accessed, OspreyInsnChunkRelation, i);
        const OspreyLogicalAccess *logical = logical_access_find(
            relations, row->pc, &row->chunk);
        if (logical == NULL) continue;
        OspreyVarPayload payload;
        memset(&payload, 0, sizeof(payload));
        payload.prim_access.chunk = row->chunk;
        payload.prim_access.insn_pc = row->pc;
        candidate_append(proposals, OSPREY_PRED_PRIMITIVE_ACCESS, &payload,
                         logical->sample_support, P_UP,
                         OSPREY_RULE_CA04);
    }
    return OSPREY_OK;
}

static OspreyStatus compile_ca04_ca05(OspreyContext *ctx)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < relations->r01_accessed->len; i++) {
        const OspreyInsnChunkRelation *target = &g_array_index(
            relations->r01_accessed, OspreyInsnChunkRelation, i);
        OspreyVarPayload target_payload;
        memset(&target_payload, 0, sizeof(target_payload));
        target_payload.chunk = target->chunk;
        uint32_t target_primitive = rule_var_id(
            ctx, OSPREY_PRED_PRIMITIVE_VAR, &target_payload);
        if (target_primitive == UINT32_MAX) continue;

        OspreyVarPayload access_payload;
        memset(&access_payload, 0, sizeof(access_payload));
        access_payload.prim_access.chunk = target->chunk;
        access_payload.prim_access.insn_pc = target->pc;
        uint32_t target_access = rule_var_id(
            ctx, OSPREY_PRED_PRIMITIVE_ACCESS, &access_payload);
        if (target_access != UINT32_MAX) {
            OspreyFactorResult result = osprey_factor_add_implication(
                ctx, OSPREY_RULE_CA04, OSPREY_GRAPH_BASE_CA, false, P_UP,
                &target_primitive, 1, target_access);
            if (result.status != OSPREY_OK) return result.status;
        }

        /* For each existing P02 at this instruction, connect to this R01
         * chunk.  Do not require the P02 chunk to equal the target chunk. */
        for (guint j = 0; j < relations->r01_accessed->len; j++) {
            const OspreyInsnChunkRelation *source = &g_array_index(
                relations->r01_accessed, OspreyInsnChunkRelation, j);
            if (source->pc != target->pc) continue;
            OspreyVarPayload source_payload;
            memset(&source_payload, 0, sizeof(source_payload));
            source_payload.prim_access.chunk = source->chunk;
            source_payload.prim_access.insn_pc = source->pc;
            uint32_t source_access = rule_var_id(
                ctx, OSPREY_PRED_PRIMITIVE_ACCESS, &source_payload);
            if (source_access == UINT32_MAX) continue;
            OspreyFactorResult result = osprey_factor_add_implication(
                ctx, OSPREY_RULE_CA05, OSPREY_GRAPH_BASE_CA, false, P_UP,
                &source_access, 1, target_primitive);
            if (result.status != OSPREY_OK) return result.status;
        }
    }
    return OSPREY_OK;
}

/* CA06: R03 plus its matching logical Access produces Scalar(v), with
 * PrimitiveAccess as the probabilistic antecedent. */
static OspreyStatus collect_ca06(OspreyContext *ctx, GArray *proposals)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < relations->r03_single_chunk->len; i++) {
        const OspreyInsnRegionRelation *group = &g_array_index(
            relations->r03_single_chunk, OspreyInsnRegionRelation, i);
        for (guint j = 0; j < relations->logical_accesses->len; j++) {
            const OspreyLogicalAccess *row = &g_array_index(
                relations->logical_accesses, OspreyLogicalAccess, j);
            if (row->pc != group->pc ||
                !same_region(&row->chunk.address.region, &group->region)) {
                continue;
            }
            double pk;
            if (!support_for_logical(ctx, row, &pk)) {
                return rules_error(ctx, OSPREY_INVALID_GRAPH);
            }
            OspreyVarPayload payload;
            memset(&payload, 0, sizeof(payload));
            payload.chunk = row->chunk;
            candidate_append(proposals, OSPREY_PRED_SCALAR, &payload,
                             row->sample_support, pk, OSPREY_RULE_CA06);
        }
    }
    return OSPREY_OK;
}

static OspreyStatus compile_ca06(OspreyContext *ctx)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < relations->r03_single_chunk->len; i++) {
        const OspreyInsnRegionRelation *group = &g_array_index(
            relations->r03_single_chunk, OspreyInsnRegionRelation, i);
        for (guint j = 0; j < relations->logical_accesses->len; j++) {
            const OspreyLogicalAccess *row = &g_array_index(
                relations->logical_accesses, OspreyLogicalAccess, j);
            if (row->pc != group->pc ||
                !same_region(&row->chunk.address.region, &group->region)) {
                continue;
            }
            OspreyVarPayload scalar_payload;
            memset(&scalar_payload, 0, sizeof(scalar_payload));
            scalar_payload.chunk = row->chunk;
            uint32_t scalar = rule_var_id(ctx, OSPREY_PRED_SCALAR,
                                          &scalar_payload);
            OspreyVarPayload access_payload;
            memset(&access_payload, 0, sizeof(access_payload));
            access_payload.prim_access.chunk = row->chunk;
            access_payload.prim_access.insn_pc = row->pc;
            uint32_t access = rule_var_id(ctx, OSPREY_PRED_PRIMITIVE_ACCESS,
                                          &access_payload);
            if (scalar == UINT32_MAX || access == UINT32_MAX) continue;
            double pk;
            if (!support_for_logical(ctx, row, &pk)) {
                return rules_error(ctx, OSPREY_INVALID_GRAPH);
            }
            OspreyFactorResult result = osprey_factor_add_implication(
                ctx, OSPREY_RULE_CA06, OSPREY_GRAPH_BASE_CA, false, pk,
                &access, 1, scalar);
            if (result.status != OSPREY_OK) return result.status;
        }
    }
    return OSPREY_OK;
}

/* CA07: adjacent chunks selected by two distinct R03 groups support one
 * another as scalars. */
static OspreyStatus compile_ca07(OspreyContext *ctx)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < relations->logical_accesses->len; i++) {
        const OspreyLogicalAccess *a = &g_array_index(
            relations->logical_accesses, OspreyLogicalAccess, i);
        if (!logical_group_contains(relations, a->pc,
                                    &a->chunk.address.region, false)) {
            continue;
        }
        for (guint j = i + 1; j < relations->logical_accesses->len; j++) {
            const OspreyLogicalAccess *b = &g_array_index(
                relations->logical_accesses, OspreyLogicalAccess, j);
            if (a->pc == b->pc ||
                !logical_group_contains(relations, b->pc,
                                        &b->chunk.address.region, false) ||
                (!osprey_relation_adjacent_chunk(&a->chunk, &b->chunk) &&
                 !osprey_relation_adjacent_chunk(&b->chunk, &a->chunk))) {
                continue;
            }
            OspreyVarPayload pa, pb;
            memset(&pa, 0, sizeof(pa));
            memset(&pb, 0, sizeof(pb));
            pa.chunk = a->chunk;
            pb.chunk = b->chunk;
            uint32_t va = rule_var_id(ctx, OSPREY_PRED_SCALAR, &pa);
            uint32_t vb = rule_var_id(ctx, OSPREY_PRED_SCALAR, &pb);
            if (va == UINT32_MAX || vb == UINT32_MAX) continue;
            double pka, pkb;
            if (!support_for_logical(ctx, a, &pka) ||
                !support_for_logical(ctx, b, &pkb)) {
                return rules_error(ctx, OSPREY_INVALID_GRAPH);
            }
            double difference = pka > pkb ? pka - pkb : pkb - pka;
            double probability = P_UP * (pka < pkb ? pka : pkb) *
                                 (1.0 - difference);
            if (probability < P_DN) probability = P_DN;
            if (probability > P_UP) probability = P_UP;
            OspreyFactorBatchResult batch = osprey_factor_add_bidirectional(
                ctx, OSPREY_RULE_CA07, OSPREY_GRAPH_BASE_CA, false,
                probability, va, vb);
            if (batch.status != OSPREY_OK) return batch.status;
        }
    }
    return OSPREY_OK;
}

/* CA08 is intentionally candidate-only: Stage 3.3 never invents a field
 * base.  Stage 3.4 calls this again after legal FieldOf candidates exist. */
static OspreyStatus compile_ca08(OspreyContext *ctx)
{
    OspreyGraph *graph = ctx->graph;
    guint variable_count = graph->vars->len;
    for (guint i = 0; i < variable_count; i++) {
        OspreyVar *field = &g_array_index(graph->vars, OspreyVar, i);
        if (field->kind != OSPREY_PRED_FIELD_OF) continue;
        OspreyVarPayload scalar_payload;
        memset(&scalar_payload, 0, sizeof(scalar_payload));
        scalar_payload.chunk = field->payload.attached.chunk;
        uint32_t scalar = rule_var_id(ctx, OSPREY_PRED_SCALAR,
                                       &scalar_payload);
        if (scalar == UINT32_MAX) continue;
        OspreyFactorBatchResult batch = osprey_factor_add_bidirectional(
            ctx, OSPREY_RULE_CA08, OSPREY_GRAPH_BASE_CA, true, P_DN,
            scalar, field->id);
        if (batch.status != OSPREY_OK) return batch.status;
    }
    return OSPREY_OK;
}

/* CB01: checked F06 geometry produces independent Array and ArrayStart
 * candidates.  The rule's deterministic evidence is represented by one
 * p_up prior for each head. */
static OspreyStatus cb01_payload(const OspreyMayArrayFact *fact,
                                 OspreyVarPayload *array_payload)
{
    uint64_t span;
    int64_t end;
    if (fact == NULL || array_payload == NULL ||
        fact->evidence_kind != OSPREY_MAY_ARRAY_CALLOC_GEOMETRY ||
        fact->element_count == 0 || fact->element_size == 0) {
        return OSPREY_INVALID_GRAPH;
    }
    if (fact->element_size > (uint64_t)INT64_MAX ||
        !osprey_check_mul(fact->element_count, fact->element_size, &span) ||
        span == 0 || span > (uint64_t)INT64_MAX ||
        !osprey_check_add(fact->start.offset, (int64_t)span, &end)) {
        return OSPREY_GRAPH_ARITHMETIC;
    }
    OspreyAddress hi = fact->start;
    hi.offset = end;
    if (!array_payload_make(&fact->start, &hi,
                            (int64_t)fact->element_size, array_payload)) {
        return OSPREY_INVALID_GRAPH;
    }
    return OSPREY_OK;
}

static OspreyStatus collect_cb01(OspreyContext *ctx, GArray *proposals)
{
    for (guint i = 0; i < ctx->mayarray_facts->len; i++) {
        const OspreyMayArrayFact *fact = &g_array_index(
            ctx->mayarray_facts, OspreyMayArrayFact, i);
        OspreyVarPayload array_payload;
        OspreyStatus status = cb01_payload(fact, &array_payload);
        if (status != OSPREY_OK) return rules_error(ctx, status);
        OspreyVarPayload start_payload;
        memset(&start_payload, 0, sizeof(start_payload));
        start_payload.addr = fact->start;
        candidate_append(proposals, OSPREY_PRED_ARRAY, &array_payload,
                         fact->sample_support, P_UP, OSPREY_RULE_CB01);
        candidate_append(proposals, OSPREY_PRED_ARRAY_START, &start_payload,
                         fact->sample_support, P_UP, OSPREY_RULE_CB01);
    }
    return OSPREY_OK;
}

static OspreyStatus compile_cb01(OspreyContext *ctx)
{
    for (guint i = 0; i < ctx->mayarray_facts->len; i++) {
        const OspreyMayArrayFact *fact = &g_array_index(
            ctx->mayarray_facts, OspreyMayArrayFact, i);
        OspreyVarPayload array_payload;
        OspreyStatus status = cb01_payload(fact, &array_payload);
        if (status != OSPREY_OK) return rules_error(ctx, status);
        OspreyVarPayload start_payload;
        memset(&start_payload, 0, sizeof(start_payload));
        start_payload.addr = fact->start;
        uint32_t array = rule_var_id(ctx, OSPREY_PRED_ARRAY,
                                     &array_payload);
        uint32_t start = rule_var_id(ctx, OSPREY_PRED_ARRAY_START,
                                     &start_payload);
        if (array != UINT32_MAX) {
            OspreyFactorResult result = osprey_factor_add_prior(
                ctx, OSPREY_RULE_CB01, OSPREY_GRAPH_SECONDARY, false, P_UP,
                array);
            if (result.status != OSPREY_OK) return result.status;
        }
        if (start != UINT32_MAX) {
            OspreyFactorResult result = osprey_factor_add_prior(
                ctx, OSPREY_RULE_CB01, OSPREY_GRAPH_SECONDARY, false, P_UP,
                start);
            if (result.status != OSPREY_OK) return result.status;
        }
    }
    return OSPREY_OK;
}

typedef struct Cb02Work {
    OspreyLogicalAccess low;
    OspreyLogicalAccess high;
    OspreyVarPayload array_payload;
} Cb02Work;

static OspreyStatus cb02_make_payload(const OspreyLogicalAccess *low,
                                      const OspreyLogicalAccess *high,
                                      OspreyVarPayload *payload,
                                      bool *valid)
{
    int64_t high_end;
    int64_t span;
    if (valid == NULL || low == NULL || high == NULL || payload == NULL) {
        return OSPREY_INVALID_GRAPH;
    }
    *valid = false;
    if (low->chunk.size == 0 || high->chunk.size == 0) {
        return OSPREY_INVALID_GRAPH;
    }
    if (low->chunk.size > (uint64_t)INT64_MAX ||
        high->chunk.size > (uint64_t)INT64_MAX) {
        return OSPREY_GRAPH_ARITHMETIC;
    }
    if (!osprey_check_add(high->chunk.address.offset,
                          (int64_t)high->chunk.size, &high_end) ||
        !osprey_check_sub(high_end, low->chunk.address.offset, &span)) {
        return OSPREY_GRAPH_ARITHMETIC;
    }
    if (span < (int64_t)low->chunk.size) return OSPREY_OK;
    OspreyAddress hi = high->chunk.address;
    hi.offset = high_end;
    if (!array_payload_make(&low->chunk.address, &hi,
                            (int64_t)low->chunk.size, payload)) {
        return OSPREY_INVALID_GRAPH;
    }
    *valid = true;
    return OSPREY_OK;
}

static OspreyStatus cb02_work_build(OspreyContext *ctx, GArray **out)
{
    const OspreyRelations *relations = ctx->relations;
    GArray *work = g_array_new(FALSE, FALSE, sizeof(Cb02Work));
    for (guint i = 0; i < relations->r04_multi_chunk->len; i++) {
        const OspreyInsnRegionRelation *group = &g_array_index(
            relations->r04_multi_chunk, OspreyInsnRegionRelation, i);
        const OspreyInsnRegionAddressRelation *low_relation =
            relation_extreme_find(relations->r06_low_address, group->pc,
                                  &group->region);
        const OspreyInsnRegionAddressRelation *high_relation =
            relation_extreme_find(relations->r05_high_address, group->pc,
                                  &group->region);
        if (low_relation == NULL || high_relation == NULL) continue;
        for (guint low_i = 0; low_i < relations->logical_accesses->len;
             low_i++) {
            const OspreyLogicalAccess *low = &g_array_index(
                relations->logical_accesses, OspreyLogicalAccess, low_i);
            if (low->pc != group->pc ||
                !same_region(&low->chunk.address.region, &group->region) ||
                low->chunk.address.offset != low_relation->address.offset) {
                continue;
            }
            for (guint high_i = 0; high_i < relations->logical_accesses->len;
                 high_i++) {
                const OspreyLogicalAccess *high = &g_array_index(
                    relations->logical_accesses, OspreyLogicalAccess, high_i);
                if (high->pc != group->pc ||
                    !same_region(&high->chunk.address.region,
                                 &group->region) ||
                    high->chunk.address.offset !=
                        high_relation->address.offset ||
                    chunk_equal(&low->chunk, &high->chunk)) {
                    continue;
                }
                Cb02Work item;
                memset(&item, 0, sizeof(item));
                bool valid;
                OspreyStatus status = cb02_make_payload(low, high,
                                                         &item.array_payload,
                                                         &valid);
                if (status != OSPREY_OK) {
                    g_array_free(work, TRUE);
                    return rules_error(ctx, status);
                }
                if (!valid) continue;
                item.low = *low;
                item.high = *high;
                g_array_append_val(work, item);
            }
        }
    }
    *out = work;
    return OSPREY_OK;
}

static OspreyStatus collect_cb02(OspreyContext *ctx, GArray *proposals)
{
    GArray *work;
    OspreyStatus status = cb02_work_build(ctx, &work);
    if (status != OSPREY_OK) return status;
    for (guint i = 0; i < work->len; i++) {
        const Cb02Work *item = &g_array_index(work, Cb02Work, i);
        uint64_t support = item->low.sample_support < item->high.sample_support
            ? item->low.sample_support : item->high.sample_support;
        candidate_append(proposals, OSPREY_PRED_ARRAY,
                         &item->array_payload, support, P_UP,
                         OSPREY_RULE_CB02);
    }
    g_array_free(work, TRUE);
    return OSPREY_OK;
}

static OspreyStatus compile_cb02(OspreyContext *ctx)
{
    GArray *work;
    OspreyStatus status = cb02_work_build(ctx, &work);
    if (status != OSPREY_OK) return status;
    for (guint i = 0; i < work->len; i++) {
        const Cb02Work *item = &g_array_index(work, Cb02Work, i);
        OspreyVarPayload low_payload;
        OspreyVarPayload high_payload;
        memset(&low_payload, 0, sizeof(low_payload));
        memset(&high_payload, 0, sizeof(high_payload));
        low_payload.prim_access.chunk = item->low.chunk;
        low_payload.prim_access.insn_pc = item->low.pc;
        high_payload.prim_access.chunk = item->high.chunk;
        high_payload.prim_access.insn_pc = item->high.pc;
        uint32_t low = rule_var_id(ctx, OSPREY_PRED_PRIMITIVE_ACCESS,
                                   &low_payload);
        uint32_t high = rule_var_id(ctx, OSPREY_PRED_PRIMITIVE_ACCESS,
                                    &high_payload);
        uint32_t array = rule_var_id(ctx, OSPREY_PRED_ARRAY,
                                     &item->array_payload);
        if (low == UINT32_MAX || high == UINT32_MAX ||
            array == UINT32_MAX) continue;
        uint32_t antecedents[2] = { low, high };
        OspreyFactorResult result = osprey_factor_add_implication(
            ctx, OSPREY_RULE_CB02, OSPREY_GRAPH_SECONDARY, false, P_UP,
            antecedents, G_N_ELEMENTS(antecedents), array);
        if (result.status != OSPREY_OK) {
            g_array_free(work, TRUE);
            return result.status;
        }
    }
    g_array_free(work, TRUE);
    return OSPREY_OK;
}

static bool base_access_matches(const OspreyRelations *relations,
                                const OspreyBaseFact *base,
                                const OspreyLogicalAccess **logical_out)
{
    if (base == NULL ||
        !logical_group_contains(relations, base->pc,
                                &base->chunk.address.region, true)) {
        return false;
    }
    const OspreyLogicalAccess *logical = logical_access_find(
        relations, base->pc, &base->chunk);
    if (logical == NULL) return false;
    if (logical_out != NULL) *logical_out = logical;
    return true;
}

static OspreyStatus collect_cb07_cb08(OspreyContext *ctx,
                                      GArray *proposals)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        const OspreyBaseFact *base = &g_array_index(ctx->base_facts,
                                                   OspreyBaseFact, i);
        const OspreyLogicalAccess *logical;
        if (!base_access_matches(relations, base, &logical)) continue;
        OspreyVarPayload payload;
        memset(&payload, 0, sizeof(payload));
        payload.addr = base->base;
        candidate_append(proposals, OSPREY_PRED_ARRAY_START, &payload,
                         logical->sample_support, P_UP,
                         OSPREY_RULE_CB07);
    }
    for (guint i = 0; i < relations->r07_most_frequent->len; i++) {
        const OspreyInsnRegionAddressRelation *most = &g_array_index(
            relations->r07_most_frequent, OspreyInsnRegionAddressRelation, i);
        if (!logical_group_contains(relations, most->pc, &most->region, true)) {
            continue;
        }
        for (guint j = 0; j < relations->logical_accesses->len; j++) {
            const OspreyLogicalAccess *logical = &g_array_index(
                relations->logical_accesses, OspreyLogicalAccess, j);
            if (logical->pc != most->pc ||
                !same_region(&logical->chunk.address.region, &most->region) ||
                !address_equal(&logical->chunk.address, &most->address) ||
                logical->dynamic_count != most->count) {
                continue;
            }
            OspreyVarPayload payload;
            memset(&payload, 0, sizeof(payload));
            payload.addr = most->address;
            candidate_append(proposals, OSPREY_PRED_ARRAY_START, &payload,
                             logical->sample_support, P_UP,
                             OSPREY_RULE_CB08);
        }
    }
    return OSPREY_OK;
}

static OspreyStatus compile_cb07_cb08(OspreyContext *ctx)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        const OspreyBaseFact *base = &g_array_index(ctx->base_facts,
                                                   OspreyBaseFact, i);
        const OspreyLogicalAccess *logical;
        if (!base_access_matches(relations, base, &logical)) continue;
        OspreyVarPayload access_payload;
        memset(&access_payload, 0, sizeof(access_payload));
        access_payload.prim_access.chunk = base->chunk;
        access_payload.prim_access.insn_pc = base->pc;
        OspreyVarPayload start_payload;
        memset(&start_payload, 0, sizeof(start_payload));
        start_payload.addr = base->base;
        uint32_t access = rule_var_id(ctx, OSPREY_PRED_PRIMITIVE_ACCESS,
                                      &access_payload);
        uint32_t start = rule_var_id(ctx, OSPREY_PRED_ARRAY_START,
                                     &start_payload);
        if (access == UINT32_MAX || start == UINT32_MAX) continue;
        OspreyFactorResult result = osprey_factor_add_implication(
            ctx, OSPREY_RULE_CB07, OSPREY_GRAPH_SECONDARY, false, P_UP,
            &access, 1, start);
        if (result.status != OSPREY_OK) return result.status;
    }
    for (guint i = 0; i < relations->r07_most_frequent->len; i++) {
        const OspreyInsnRegionAddressRelation *most = &g_array_index(
            relations->r07_most_frequent, OspreyInsnRegionAddressRelation, i);
        if (!logical_group_contains(relations, most->pc, &most->region, true)) {
            continue;
        }
        for (guint j = 0; j < relations->logical_accesses->len; j++) {
            const OspreyLogicalAccess *logical = &g_array_index(
                relations->logical_accesses, OspreyLogicalAccess, j);
            if (logical->pc != most->pc ||
                !same_region(&logical->chunk.address.region, &most->region) ||
                !address_equal(&logical->chunk.address, &most->address) ||
                logical->dynamic_count != most->count) {
                continue;
            }
            OspreyVarPayload access_payload;
            memset(&access_payload, 0, sizeof(access_payload));
            access_payload.prim_access.chunk = logical->chunk;
            access_payload.prim_access.insn_pc = logical->pc;
            OspreyVarPayload start_payload;
            memset(&start_payload, 0, sizeof(start_payload));
            start_payload.addr = most->address;
            uint32_t access = rule_var_id(ctx, OSPREY_PRED_PRIMITIVE_ACCESS,
                                          &access_payload);
            uint32_t start = rule_var_id(ctx, OSPREY_PRED_ARRAY_START,
                                         &start_payload);
            if (access == UINT32_MAX || start == UINT32_MAX) continue;
            double pk;
            if (!support_for_logical(ctx, logical, &pk)) {
                return rules_error(ctx, OSPREY_INVALID_GRAPH);
            }
            OspreyFactorResult result = osprey_factor_add_implication(
                ctx, OSPREY_RULE_CB08, OSPREY_GRAPH_SECONDARY, false, pk,
                &access, 1, start);
            if (result.status != OSPREY_OK) return result.status;
        }
    }
    return OSPREY_OK;
}

static OspreyStatus compile_cb09(OspreyContext *ctx)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < relations->logical_accesses->len; i++) {
        const OspreyLogicalAccess *a = &g_array_index(
            relations->logical_accesses, OspreyLogicalAccess, i);
        for (guint j = i + 1; j < relations->logical_accesses->len; j++) {
            const OspreyLogicalAccess *b = &g_array_index(
                relations->logical_accesses, OspreyLogicalAccess, j);
            if (a->pc != b->pc ||
                !same_region(&a->chunk.address.region,
                             &b->chunk.address.region) ||
                a->chunk.address.offset >= b->chunk.address.offset) {
                continue;
            }
            OspreyVarPayload pa, pb;
            memset(&pa, 0, sizeof(pa));
            memset(&pb, 0, sizeof(pb));
            pa.addr = a->chunk.address;
            pb.addr = b->chunk.address;
            uint32_t first = rule_var_id(ctx, OSPREY_PRED_ARRAY_START, &pa);
            uint32_t second = rule_var_id(ctx, OSPREY_PRED_ARRAY_START, &pb);
            if (first == UINT32_MAX || second == UINT32_MAX) continue;
            OspreyFactorResult result = osprey_factor_add_implication(
                ctx, OSPREY_RULE_CB09, OSPREY_GRAPH_SECONDARY, true, P_DN,
                &first, 1, second);
            if (result.status != OSPREY_OK) return result.status;
        }
    }
    return OSPREY_OK;
}

static OspreyStatus collect_initial_ca_cb(OspreyContext *ctx,
                                          GArray *proposals)
{
    OspreyStatus status;
    status = collect_ca01(ctx, proposals);
    if (status != OSPREY_OK) return status;
    status = collect_ca04_ca05(ctx, proposals);
    if (status != OSPREY_OK) return status;
    status = collect_ca06(ctx, proposals);
    if (status != OSPREY_OK) return status;
    status = collect_cb01(ctx, proposals);
    if (status != OSPREY_OK) return status;
    status = collect_cb02(ctx, proposals);
    if (status != OSPREY_OK) return status;
    return collect_cb07_cb08(ctx, proposals);
}

static OspreyStatus compile_initial_ca_cb(OspreyContext *ctx)
{
    OspreyStatus status;
    status = compile_ca01(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_ca02_ca03(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_ca04_ca05(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_ca06(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_ca07(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_cb01(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_cb02(ctx);
    if (status != OSPREY_OK) return status;
    return compile_cb07_cb08(ctx);
}

/* CC01/CC02 candidate collection and factor compilation.  R08 and R09
 * already contain the successful-size classification; do not rescan raw
 * allocator observations or emit CC02 for a singleton site. */
static OspreyStatus collect_cc01_cc02(OspreyContext *ctx,
                                      GArray *proposals)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < relations->r08_constant_alloc->len; i++) {
        const OspreyAllocRelation *row = &g_array_index(
            relations->r08_constant_alloc, OspreyAllocRelation, i);
        if (row->size > (uint64_t)INT64_MAX) {
            return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
        }
        OspreyRegionId region;
        memset(&region, 0, sizeof(region));
        region.kind = OSPREY_REGION_HEAP_SITE;
        region.site_offset = row->site_pc;
        OspreyVarPayload unfoldable;
        OspreyVarPayload foldable_zero;
        memset(&unfoldable, 0, sizeof(unfoldable));
        memset(&foldable_zero, 0, sizeof(foldable_zero));
        unfoldable.heap_fold.region = region;
        unfoldable.heap_fold.size = row->size;
        foldable_zero.heap_fold.region = region;
        foldable_zero.heap_fold.size = 0;
        candidate_append(proposals, OSPREY_PRED_UNFOLDABLE_HEAP,
                         &unfoldable, 1, P_UP, OSPREY_RULE_CC01);
        candidate_append(proposals, OSPREY_PRED_FOLDABLE_HEAP,
                         &foldable_zero, 1, P_UP, OSPREY_RULE_CC01);
    }
    for (guint i = 0; i < relations->r09_alloc_unit->len; i++) {
        const OspreyAllocRelation *row = &g_array_index(
            relations->r09_alloc_unit, OspreyAllocRelation, i);
        if (row->size == 0 || row->size > (uint64_t)INT64_MAX) {
            return rules_error(ctx, row->size == 0
                               ? OSPREY_INVALID_GRAPH
                               : OSPREY_GRAPH_ARITHMETIC);
        }
        OspreyRegionId region;
        memset(&region, 0, sizeof(region));
        region.kind = OSPREY_REGION_HEAP_SITE;
        region.site_offset = row->site_pc;
        OspreyVarPayload foldable;
        memset(&foldable, 0, sizeof(foldable));
        foldable.heap_fold.region = region;
        foldable.heap_fold.size = row->size;
        candidate_append(proposals, OSPREY_PRED_FOLDABLE_HEAP,
                         &foldable, 1, P_UP, OSPREY_RULE_CC02);
    }
    return OSPREY_OK;
}

static OspreyStatus compile_cc01_cc02(OspreyContext *ctx)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < relations->r08_constant_alloc->len; i++) {
        const OspreyAllocRelation *row = &g_array_index(
            relations->r08_constant_alloc, OspreyAllocRelation, i);
        OspreyRegionId region;
        memset(&region, 0, sizeof(region));
        region.kind = OSPREY_REGION_HEAP_SITE;
        region.site_offset = row->site_pc;
        OspreyVarPayload unfoldable;
        OspreyVarPayload foldable_zero;
        memset(&unfoldable, 0, sizeof(unfoldable));
        memset(&foldable_zero, 0, sizeof(foldable_zero));
        unfoldable.heap_fold.region = region;
        unfoldable.heap_fold.size = row->size;
        foldable_zero.heap_fold.region = region;
        foldable_zero.heap_fold.size = 0;
        uint32_t unfoldable_id = rule_var_id(
            ctx, OSPREY_PRED_UNFOLDABLE_HEAP, &unfoldable);
        uint32_t zero_id = rule_var_id(
            ctx, OSPREY_PRED_FOLDABLE_HEAP, &foldable_zero);
        if (unfoldable_id == UINT32_MAX || zero_id == UINT32_MAX) {
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        OspreyFactorResult result = osprey_factor_add_prior(
            ctx, OSPREY_RULE_CC01, OSPREY_GRAPH_SECONDARY, false, P_UP,
            unfoldable_id);
        if (result.status != OSPREY_OK) return result.status;
        result = osprey_factor_add_prior(
            ctx, OSPREY_RULE_CC01, OSPREY_GRAPH_SECONDARY, false, P_UP,
            zero_id);
        if (result.status != OSPREY_OK) return result.status;
    }
    for (guint i = 0; i < relations->r09_alloc_unit->len; i++) {
        const OspreyAllocRelation *row = &g_array_index(
            relations->r09_alloc_unit, OspreyAllocRelation, i);
        OspreyRegionId region;
        memset(&region, 0, sizeof(region));
        region.kind = OSPREY_REGION_HEAP_SITE;
        region.site_offset = row->site_pc;
        OspreyVarPayload foldable;
        memset(&foldable, 0, sizeof(foldable));
        foldable.heap_fold.region = region;
        foldable.heap_fold.size = row->size;
        uint32_t id = rule_var_id(ctx, OSPREY_PRED_FOLDABLE_HEAP,
                                  &foldable);
        if (id == UINT32_MAX) return rules_error(ctx, OSPREY_INVALID_GRAPH);
        OspreyFactorResult result = osprey_factor_add_prior(
            ctx, OSPREY_RULE_CC02, OSPREY_GRAPH_SECONDARY, false, P_UP, id);
        if (result.status != OSPREY_OK) return result.status;
    }
    return OSPREY_OK;
}

/* CC03: PrimitiveVar(v) in heap H_i -> UnfoldableHeap(i, o+s). */
static OspreyStatus collect_cc03(OspreyContext *ctx, GArray *proposals)
{
    OspreyGraph *graph = ctx->graph;
    for (guint i = 0; i < graph->vars->len; i++) {
        const OspreyVar *primitive = &g_array_index(graph->vars,
                                                    OspreyVar, i);
        if (primitive->kind != OSPREY_PRED_PRIMITIVE_VAR ||
            primitive->payload.chunk.address.region.kind !=
                OSPREY_REGION_HEAP_SITE) {
            continue;
        }
        if (primitive->payload.chunk.size > (uint64_t)INT64_MAX) {
            return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
        }
        int64_t end;
        if (!osprey_check_add(primitive->payload.chunk.address.offset,
                              (int64_t)primitive->payload.chunk.size, &end)) {
            return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
        }
        if (primitive->payload.chunk.address.offset < 0 || end < 0) {
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        OspreyVarPayload payload;
        memset(&payload, 0, sizeof(payload));
        payload.heap_fold.region = primitive->payload.chunk.address.region;
        payload.heap_fold.size = (uint64_t)end;
        candidate_append(proposals, OSPREY_PRED_UNFOLDABLE_HEAP, &payload,
                         primitive->direct_support, P_UP,
                         OSPREY_RULE_CC03);
    }
    return OSPREY_OK;
}

static OspreyStatus compile_cc03(OspreyContext *ctx)
{
    OspreyGraph *graph = ctx->graph;
    for (guint i = 0; i < graph->vars->len; i++) {
        const OspreyVar *primitive = &g_array_index(graph->vars,
                                                    OspreyVar, i);
        if (primitive->kind != OSPREY_PRED_PRIMITIVE_VAR ||
            primitive->payload.chunk.address.region.kind !=
                OSPREY_REGION_HEAP_SITE) {
            continue;
        }
        if (primitive->payload.chunk.size > (uint64_t)INT64_MAX) {
            return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
        }
        int64_t end;
        if (!osprey_check_add(primitive->payload.chunk.address.offset,
                              (int64_t)primitive->payload.chunk.size, &end) ||
            end < 0) {
            return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
        }
        OspreyVarPayload payload;
        memset(&payload, 0, sizeof(payload));
        payload.heap_fold.region = primitive->payload.chunk.address.region;
        payload.heap_fold.size = (uint64_t)end;
        uint32_t unfoldable = rule_var_id(
            ctx, OSPREY_PRED_UNFOLDABLE_HEAP, &payload);
        if (unfoldable == UINT32_MAX) {
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        uint32_t ids[2] = { primitive->id, unfoldable };
        OspreyFactorResult result = osprey_factor_add_implication(
            ctx, OSPREY_RULE_CC03, OSPREY_GRAPH_SECONDARY, false, P_UP,
            &ids[0], 1, ids[1]);
        if (result.status != OSPREY_OK) return result.status;
    }
    return OSPREY_OK;
}

static const OspreyLogicalAccess *logical_chunk_find(
    const OspreyRelations *relations, const OspreyChunk *chunk)
{
    if (relations == NULL || chunk == NULL) return NULL;
    for (guint i = 0; i < relations->logical_accesses->len; i++) {
        const OspreyLogicalAccess *row = &g_array_index(
            relations->logical_accesses, OspreyLogicalAccess, i);
        if (chunk_equal(&row->chunk, chunk)) return row;
    }
    return NULL;
}

/* A CD06 field candidate is legal only when the accessed source chunk is at
 * a checked nonnegative offset from the matched target base.  The complete
 * field span is validated against the merged region extent when the
 * candidate is selected; every accessed target width remains a separate
 * implication witness.  Relation mismatches are ordinary near misses;
 * checked arithmetic failures reject the graph. */
static OspreyStatus cd06_field_legal(const OspreyBaseFact *base,
                                     const OspreyChunkRelation *target,
                                     bool *legal)
{
    if (base == NULL || target == NULL || legal == NULL) {
        return OSPREY_INVALID_GRAPH;
    }
    *legal = false;
    if (base->chunk.size > (uint64_t)INT64_MAX ||
        target->chunk.size > (uint64_t)INT64_MAX) {
        return OSPREY_GRAPH_ARITHMETIC;
    }
    int64_t relative;
    int64_t source_end;
    int64_t base_end;
    if (!osprey_check_sub(base->chunk.address.offset,
                          target->chunk.address.offset, &relative) ||
        !osprey_check_add(base->chunk.address.offset,
                          (int64_t)base->chunk.size, &source_end) ||
        !osprey_check_add(target->chunk.address.offset,
                          (int64_t)base->chunk.size, &base_end)) {
        return OSPREY_GRAPH_ARITHMETIC;
    }
    (void)source_end;
    (void)base_end;
    if (relative < 0) return OSPREY_OK;
    *legal = true;
    return OSPREY_OK;
}

static OspreyStatus collect_cd06(OspreyContext *ctx, GArray *proposals)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        const OspreyBaseFact *base = &g_array_index(
            ctx->base_facts, OspreyBaseFact, i);
        if (logical_chunk_find(relations, &base->chunk) == NULL) {
            continue;
        }
        for (guint j = 0; j < relations->r02_accessed->len; j++) {
            const OspreyChunkRelation *target = &g_array_index(
                relations->r02_accessed, OspreyChunkRelation, j);
            if (!address_equal(&target->chunk.address, &base->base) ||
                !same_region(&base->chunk.address.region,
                             &target->chunk.address.region)) {
                continue;
            }
            bool legal;
            OspreyStatus legal_status = cd06_field_legal(base, target,
                                                          &legal);
            if (legal_status != OSPREY_OK) {
                return rules_error(ctx, legal_status);
            }
            if (!legal) continue;
            OspreyVarPayload field;
            memset(&field, 0, sizeof(field));
            field.attached.chunk = base->chunk;
            field.attached.base = target->chunk.address;
            candidate_append(proposals, OSPREY_PRED_FIELD_OF, &field, 1,
                             P_UP, OSPREY_RULE_CD06);
        }
    }
    return OSPREY_OK;
}

static OspreyStatus compile_cd06(OspreyContext *ctx)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        const OspreyBaseFact *base = &g_array_index(
            ctx->base_facts, OspreyBaseFact, i);
        if (logical_chunk_find(relations, &base->chunk) == NULL) {
            continue;
        }
        OspreyVarPayload source_payload;
        memset(&source_payload, 0, sizeof(source_payload));
        source_payload.chunk = base->chunk;
        uint32_t source = rule_var_id(ctx, OSPREY_PRED_PRIMITIVE_VAR,
                                      &source_payload);
        if (source == UINT32_MAX) {
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        for (guint j = 0; j < relations->r02_accessed->len; j++) {
            const OspreyChunkRelation *target = &g_array_index(
                relations->r02_accessed, OspreyChunkRelation, j);
            if (!address_equal(&target->chunk.address, &base->base) ||
                !same_region(&base->chunk.address.region,
                             &target->chunk.address.region)) {
                continue;
            }
            bool legal;
            OspreyStatus legal_status = cd06_field_legal(base, target,
                                                          &legal);
            if (legal_status != OSPREY_OK) {
                return rules_error(ctx, legal_status);
            }
            if (!legal) continue;
            OspreyVarPayload target_payload;
            OspreyVarPayload field_payload;
            memset(&target_payload, 0, sizeof(target_payload));
            memset(&field_payload, 0, sizeof(field_payload));
            target_payload.chunk = target->chunk;
            field_payload.attached.chunk = base->chunk;
            field_payload.attached.base = target->chunk.address;
            uint32_t target_var_id = rule_var_id(
                ctx, OSPREY_PRED_PRIMITIVE_VAR, &target_payload);
            uint32_t field = rule_var_id(ctx, OSPREY_PRED_FIELD_OF,
                                         &field_payload);
            if (target_var_id == UINT32_MAX || field == UINT32_MAX) {
                return rules_error(ctx, OSPREY_INVALID_GRAPH);
            }
            uint32_t antecedents[2] = { source, target_var_id };
            uint32_t num_antecedents = source == target_var_id ? 1 : 2;
            OspreyFactorResult result = osprey_factor_add_implication(
                ctx, OSPREY_RULE_CD06, OSPREY_GRAPH_SECONDARY, false, P_UP,
                antecedents, num_antecedents, field);
            if (result.status != OSPREY_OK) return result.status;
        }
    }
    return OSPREY_OK;
}

/* CD11: PointsTo(v1, v2.a) plus access of both chunks -> Pointer(v1,v2.a). */
static OspreyStatus collect_cd11(OspreyContext *ctx, GArray *proposals)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < ctx->points_facts->len; i++) {
        const OspreyPointsToFact *points = &g_array_index(
            ctx->points_facts, OspreyPointsToFact, i);
        if (logical_chunk_find(relations, &points->pointer_chunk) == NULL) {
            continue;
        }
        for (guint j = 0; j < relations->r02_accessed->len; j++) {
            const OspreyChunkRelation *target = &g_array_index(
                relations->r02_accessed, OspreyChunkRelation, j);
            if (!address_equal(&target->chunk.address, &points->target)) {
                continue;
            }
            OspreyVarPayload pointer;
            memset(&pointer, 0, sizeof(pointer));
            pointer.attached.chunk = points->pointer_chunk;
            pointer.attached.base = target->chunk.address;
            candidate_append(proposals, OSPREY_PRED_POINTER, &pointer, 1,
                             P_UP, OSPREY_RULE_CD11);
        }
    }
    return OSPREY_OK;
}

static OspreyStatus compile_cd11(OspreyContext *ctx)
{
    const OspreyRelations *relations = ctx->relations;
    for (guint i = 0; i < ctx->points_facts->len; i++) {
        const OspreyPointsToFact *points = &g_array_index(
            ctx->points_facts, OspreyPointsToFact, i);
        if (logical_chunk_find(relations, &points->pointer_chunk) == NULL) {
            continue;
        }
        OspreyVarPayload pointer_payload;
        memset(&pointer_payload, 0, sizeof(pointer_payload));
        pointer_payload.chunk = points->pointer_chunk;
        uint32_t pointer_primitive = rule_var_id(
            ctx, OSPREY_PRED_PRIMITIVE_VAR, &pointer_payload);
        if (pointer_primitive == UINT32_MAX) {
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        for (guint j = 0; j < relations->r02_accessed->len; j++) {
            const OspreyChunkRelation *target = &g_array_index(
                relations->r02_accessed, OspreyChunkRelation, j);
            if (!address_equal(&target->chunk.address, &points->target)) {
                continue;
            }
            OspreyVarPayload target_payload;
            OspreyVarPayload pointer;
            memset(&target_payload, 0, sizeof(target_payload));
            memset(&pointer, 0, sizeof(pointer));
            target_payload.chunk = target->chunk;
            pointer.attached.chunk = points->pointer_chunk;
            pointer.attached.base = target->chunk.address;
            uint32_t target_var_id = rule_var_id(
                ctx, OSPREY_PRED_PRIMITIVE_VAR, &target_payload);
            uint32_t pointer_id = rule_var_id(ctx, OSPREY_PRED_POINTER,
                                              &pointer);
            if (target_var_id == UINT32_MAX || pointer_id == UINT32_MAX) {
                return rules_error(ctx, OSPREY_INVALID_GRAPH);
            }
            uint32_t antecedents[2] = {
                pointer_primitive, target_var_id
            };
            uint32_t num_antecedents =
                pointer_primitive == target_var_id ? 1 : 2;
            OspreyFactorResult result = osprey_factor_add_implication(
                ctx, OSPREY_RULE_CD11, OSPREY_GRAPH_SECONDARY, false, P_UP,
                antecedents, num_antecedents, pointer_id);
            if (result.status != OSPREY_OK) return result.status;
        }
    }
    return OSPREY_OK;
}

/* CD10: FieldOf(v,a1) ↔ p_down FieldOf(v,a2) for distinct bases. */
static OspreyStatus compile_cd10(OspreyContext *ctx)
{
    OspreyGraph *graph = ctx->graph;
    for (guint i = 0; i < graph->vars->len; i++) {
        const OspreyVar *first = &g_array_index(graph->vars, OspreyVar, i);
        if (first->kind != OSPREY_PRED_FIELD_OF) continue;
        for (guint j = i + 1; j < graph->vars->len; j++) {
            const OspreyVar *second = &g_array_index(graph->vars,
                                                     OspreyVar, j);
            if (second->kind != OSPREY_PRED_FIELD_OF ||
                !chunk_equal(&first->payload.attached.chunk,
                             &second->payload.attached.chunk) ||
                address_equal(&first->payload.attached.base,
                              &second->payload.attached.base)) {
                continue;
            }
            OspreyFactorBatchResult result = osprey_factor_add_bidirectional(
                ctx, OSPREY_RULE_CD10, OSPREY_GRAPH_SECONDARY, true, P_DN,
                first->id, second->id);
            if (result.status != OSPREY_OK) return result.status;
        }
    }
    return OSPREY_OK;
}

/* CD01/CD02/CD03: R10/R12/R11 hint -> HomoSegment. */
static bool cd_hint_rule(uint8_t kind, uint16_t *rule)
{
    if (rule == NULL) return false;
    switch (kind) {
    case OSPREY_RELATION_DATA_FLOW:
        *rule = OSPREY_RULE_CD01;
        return true;
    case OSPREY_RELATION_POINTS_TO:
        *rule = OSPREY_RULE_CD02;
        return true;
    case OSPREY_RELATION_UNIFIED_ACCESS:
        *rule = OSPREY_RULE_CD03;
        return true;
    default:
        return false;
    }
}

static OspreyStatus collect_cd01_03(OspreyContext *ctx, GArray *proposals)
{
    for (guint i = 0; i < ctx->graph->hints->len; i++) {
        const OspreyHint *hint = &g_array_index(ctx->graph->hints,
                                                OspreyHint, i);
        uint16_t rule;
        if (!cd_hint_rule(hint->kind, &rule)) {
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        OspreyVarPayload payload;
        memset(&payload, 0, sizeof(payload));
        payload.segment.a1 = hint->a1;
        payload.segment.a2 = hint->a2;
        payload.segment.size = hint->size;
        /* p_s is the fixed Stage-3 p_up.  Witness counts stay diagnostic. */
        candidate_append(proposals, OSPREY_PRED_HOMO_SEGMENT, &payload, 1,
                         P_UP, rule);
    }
    return OSPREY_OK;
}

static OspreyStatus compile_cd01_03(OspreyContext *ctx)
{
    for (guint i = 0; i < ctx->graph->hints->len; i++) {
        const OspreyHint *hint = &g_array_index(ctx->graph->hints,
                                                OspreyHint, i);
        uint16_t rule;
        if (!cd_hint_rule(hint->kind, &rule)) {
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        OspreyVarPayload payload;
        memset(&payload, 0, sizeof(payload));
        payload.segment.a1 = hint->a1;
        payload.segment.a2 = hint->a2;
        payload.segment.size = hint->size;
        uint32_t homo = rule_var_id(ctx, OSPREY_PRED_HOMO_SEGMENT, &payload);
        if (homo == UINT32_MAX) return rules_error(ctx, OSPREY_INVALID_GRAPH);
        OspreyFactorResult result = osprey_factor_add_prior(
            ctx, rule, OSPREY_GRAPH_SECONDARY, false, P_UP, homo);
        if (result.status != OSPREY_OK) return result.status;
    }
    return OSPREY_OK;
}

typedef struct Cd04PairKey {
    uint32_t first;
    uint32_t second;
} Cd04PairKey;

typedef struct Cd04UnionKey {
    uint32_t first;
    uint32_t second;
    OspreyVarPayload payload;
} Cd04UnionKey;

typedef struct Cd04UnionWork {
    uint32_t first;
    uint32_t second;
    uint8_t candidate_new;
    uint8_t reserved[3];
    OspreyVarPayload payload;
} Cd04UnionWork;

static bool rule_witness_mark(GHashTable *seen, const void *data, gsize size)
{
    GBytes *key = g_bytes_new(data, size);
    if (g_hash_table_contains(seen, key)) {
        g_bytes_unref(key);
        return false;
    }
    g_hash_table_add(seen, key);
    return true;
}

static int cd04_homo_id_compare(gconstpointer ap, gconstpointer bp,
                                gpointer user_data)
{
    const OspreyGraph *graph = user_data;
    uint32_t a_id = *(const uint32_t *)ap;
    uint32_t b_id = *(const uint32_t *)bp;
    const OspreyVar *a = &g_array_index(graph->vars, OspreyVar, a_id);
    const OspreyVar *b = &g_array_index(graph->vars, OspreyVar, b_id);
    int result;
    result = (a->payload.segment.a1.region.kind !=
              b->payload.segment.a1.region.kind)
        ? (a->payload.segment.a1.region.kind <
           b->payload.segment.a1.region.kind ? -1 : 1) : 0;
    if (result == 0 && a->payload.segment.a1.region.code_image_id !=
                       b->payload.segment.a1.region.code_image_id) {
        result = a->payload.segment.a1.region.code_image_id <
                 b->payload.segment.a1.region.code_image_id ? -1 : 1;
    }
    if (result == 0 && a->payload.segment.a1.region.site_offset !=
                       b->payload.segment.a1.region.site_offset) {
        result = a->payload.segment.a1.region.site_offset <
                 b->payload.segment.a1.region.site_offset ? -1 : 1;
    }
    if (result == 0 && a->payload.segment.a1.offset !=
                       b->payload.segment.a1.offset) {
        result = a->payload.segment.a1.offset <
                 b->payload.segment.a1.offset ? -1 : 1;
    }
    if (result == 0 && a->payload.segment.a2.region.kind !=
                       b->payload.segment.a2.region.kind) {
        result = a->payload.segment.a2.region.kind <
                 b->payload.segment.a2.region.kind ? -1 : 1;
    }
    if (result == 0 && a->payload.segment.a2.region.code_image_id !=
                       b->payload.segment.a2.region.code_image_id) {
        result = a->payload.segment.a2.region.code_image_id <
                 b->payload.segment.a2.region.code_image_id ? -1 : 1;
    }
    if (result == 0 && a->payload.segment.a2.region.site_offset !=
                       b->payload.segment.a2.region.site_offset) {
        result = a->payload.segment.a2.region.site_offset <
                 b->payload.segment.a2.region.site_offset ? -1 : 1;
    }
    if (result == 0 && a->payload.segment.a2.offset !=
                       b->payload.segment.a2.offset) {
        result = a->payload.segment.a2.offset <
                 b->payload.segment.a2.offset ? -1 : 1;
    }
    if (result == 0 && a->payload.segment.size != b->payload.segment.size) {
        result = a->payload.segment.size < b->payload.segment.size ? -1 : 1;
    }
    return result != 0 ? result : (a_id < b_id ? -1 : a_id != b_id);
}

static OspreyStatus cd04_try_pair(OspreyContext *ctx,
                                  const OspreyVar *first,
                                  const OspreyVar *second,
                                  bool reverse_second,
                                  GHashTable *pair_seen,
                                  GHashTable *union_seen,
                                  GArray *pairs, GArray *unions,
                                  GArray *proposals)
{
    const OspreyAddress *second_start = reverse_second
        ? &second->payload.segment.a2 : &second->payload.segment.a1;
    const OspreyAddress *second_partner = reverse_second
        ? &second->payload.segment.a1 : &second->payload.segment.a2;
    if (!same_region_addr(&first->payload.segment.a1, second_start) ||
        !same_region_addr(&first->payload.segment.a2, second_partner)) {
        return OSPREY_OK;
    }
    int64_t delta;
    int64_t partner_delta;
    if (!offset_between(second_start, &first->payload.segment.a1, &delta) ||
        !offset_between(second_partner, &first->payload.segment.a2,
                        &partner_delta)) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }
    if (delta != partner_delta || delta <= 0 ||
        delta >= first->payload.segment.size) {
        return OSPREY_OK;
    }
    int64_t union_size;
    if (!osprey_check_add(delta, second->payload.segment.size,
                          &union_size)) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }
    if (union_size <= 0) return rules_error(ctx, OSPREY_INVALID_GRAPH);
    int64_t end;
    if (!osprey_check_add(first->payload.segment.a1.offset, union_size,
                          &end) ||
        !osprey_check_add(first->payload.segment.a2.offset, union_size,
                          &end)) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }

    Cd04PairKey seen_pair = {
        first->id < second->id ? first->id : second->id,
        first->id < second->id ? second->id : first->id
    };
    if (rule_witness_mark(pair_seen, &seen_pair, sizeof(seen_pair))) {
        /* `pairs` carries endpoint-canonical roles; using allocation IDs
         * here would make the directional factors depend on insertion
         * order. */
        Cd04PairKey pair = { first->id, second->id };
        g_array_append_val(pairs, pair);
    }

    Cd04UnionWork work;
    memset(&work, 0, sizeof(work));
    work.first = first->id;
    work.second = second->id;
    work.payload.segment.a1 = first->payload.segment.a1;
    work.payload.segment.a2 = first->payload.segment.a2;
    work.payload.segment.size = union_size;
    Cd04UnionKey union_key;
    memset(&union_key, 0, sizeof(union_key));
    union_key.first = work.first < work.second ? work.first : work.second;
    union_key.second = work.first < work.second ? work.second : work.first;
    union_key.payload = work.payload;
    if (rule_witness_mark(union_seen, &union_key, sizeof(union_key))) {
        OspreyVarPayload canonical = work.payload;
        work.candidate_new = rule_var_id(
            ctx, OSPREY_PRED_HOMO_SEGMENT, &canonical) == UINT32_MAX;
        g_array_append_val(unions, work);
        if (work.candidate_new) {
            candidate_append(proposals, OSPREY_PRED_HOMO_SEGMENT,
                             &work.payload, 1, P_UP, OSPREY_RULE_CD04);
        }
    }
    return OSPREY_OK;
}

/* CD04 static candidate closure.  P05 candidates, rather than raw hints,
 * are the inputs; correspondence is checked on both endpoint regions. */
static OspreyStatus cd04_round(OspreyContext *ctx, GHashTable *pair_seen,
                               GHashTable *union_seen, bool *changed)
{
    OspreyGraph *graph = ctx->graph;
    guint vars_before = graph->vars->len;
    guint factors_before = graph->factors->len;
    GArray *ids = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    GArray *pairs = g_array_new(FALSE, FALSE, sizeof(Cd04PairKey));
    GArray *unions = g_array_new(FALSE, FALSE, sizeof(Cd04UnionWork));
    GArray *proposals = g_array_new(FALSE, FALSE,
                                    sizeof(OspreyCandidateProposal));
    for (guint i = 0; i < graph->vars->len; i++) {
        const OspreyVar *variable = &g_array_index(graph->vars, OspreyVar, i);
        if (variable->kind == OSPREY_PRED_HOMO_SEGMENT) {
            uint32_t id = variable->id;
            g_array_append_val(ids, id);
        }
    }
    g_array_sort_with_data(ids, cd04_homo_id_compare, graph);
    OspreyStatus status = OSPREY_OK;
    for (guint i = 0; i < ids->len && status == OSPREY_OK; i++) {
        const OspreyVar *first = &g_array_index(
            graph->vars, OspreyVar, g_array_index(ids, uint32_t, i));
        for (guint j = i + 1; j < ids->len && status == OSPREY_OK; j++) {
            const OspreyVar *second = &g_array_index(
                graph->vars, OspreyVar, g_array_index(ids, uint32_t, j));
            status = cd04_try_pair(ctx, first, second, false, pair_seen,
                                   union_seen, pairs, unions, proposals);
            if (status == OSPREY_OK) {
                status = cd04_try_pair(ctx, first, second, true, pair_seen,
                                       union_seen, pairs, unions, proposals);
            }
            if (status == OSPREY_OK) {
                status = cd04_try_pair(ctx, second, first, false, pair_seen,
                                       union_seen, pairs, unions, proposals);
            }
            if (status == OSPREY_OK) {
                status = cd04_try_pair(ctx, second, first, true, pair_seen,
                                       union_seen, pairs, unions, proposals);
            }
        }
    }
    if (status == OSPREY_OK && proposals->len != 0) {
        status = select_new_candidates(ctx, proposals);
    }
    for (guint i = 0; i < pairs->len && status == OSPREY_OK; i++) {
        const Cd04PairKey *pair = &g_array_index(pairs, Cd04PairKey, i);
        OspreyFactorBatchResult result = osprey_factor_add_bidirectional(
            ctx, OSPREY_RULE_CD04, OSPREY_GRAPH_SECONDARY, false, P_UP,
            pair->first, pair->second);
        if (result.status != OSPREY_OK) status = result.status;
    }
    for (guint i = 0; i < unions->len && status == OSPREY_OK; i++) {
        const Cd04UnionWork *work = &g_array_index(unions, Cd04UnionWork, i);
        uint32_t derived = rule_var_id(ctx, OSPREY_PRED_HOMO_SEGMENT,
                                       &work->payload);
        if (derived == UINT32_MAX) {
            status = rules_error(ctx, OSPREY_INVALID_GRAPH);
            break;
        }
        if (derived == work->first || derived == work->second) continue;
        uint32_t antecedents[2] = { work->first, work->second };
        OspreyFactorResult result = osprey_factor_add_implication(
            ctx, OSPREY_RULE_CD04, OSPREY_GRAPH_SECONDARY, false, P_UP,
            antecedents, G_N_ELEMENTS(antecedents), derived);
        if (result.status != OSPREY_OK) status = result.status;
    }
    if (status == OSPREY_OK) {
        for (guint i = 0; i < unions->len; i++) {
            const Cd04UnionWork *work = &g_array_index(
                unions, Cd04UnionWork, i);
            if (work->candidate_new) {
                if (graph->cd04_extensions == UINT64_MAX) {
                    status = rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
                    break;
                }
                graph->cd04_extensions++;
            }
        }
    }
    *changed = graph->vars->len != vars_before ||
               graph->factors->len != factors_before;
    g_array_free(proposals, TRUE);
    g_array_free(unions, TRUE);
    g_array_free(pairs, TRUE);
    g_array_free(ids, TRUE);
    return status;
}

/* ------------------------------------------------------------------ */
/* Secondary deterministic closure                                  */
/* ------------------------------------------------------------------ */

/* Array var helpers: extract (lo, hi, stride) from the segment payload. */
static bool array_interval(const OspreyVar *v, const OspreyAddress **lo,
                           const OspreyAddress **hi, int64_t *stride)
{
    int64_t span;
    if (v == NULL || v->kind != OSPREY_PRED_ARRAY) return false;
    *lo = &v->payload.segment.a1;
    *hi = &v->payload.segment.a2;
    *stride = v->payload.segment.size;
    return *stride > 0 && same_region_addr(*lo, *hi) &&
           (*lo)->offset < (*hi)->offset &&
           osprey_check_sub((*hi)->offset, (*lo)->offset, &span) &&
           span >= *stride;
}

/* CB07/CB08: ArrayStart support from BaseAddr / most-frequent access. */


typedef enum ArrayDerivedKind {
    ARRAY_DERIVED_CB03_UNION = 1,
    ARRAY_DERIVED_CB04_LEFT = 2,
    ARRAY_DERIVED_CB04_RIGHT = 3,
    ARRAY_DERIVED_CB05_LEFT = 4,
    ARRAY_DERIVED_CB05_RIGHT = 5,
} ArrayDerivedKind;

typedef struct ArrayDerivedWork {
    uint8_t kind;
    uint8_t reserved[3];
    uint32_t first;
    uint32_t second;
    OspreyVarPayload payload;
} ArrayDerivedWork;

typedef enum ArrayPairKind {
    ARRAY_PAIR_CB03 = 1,
    ARRAY_PAIR_CB04 = 2,
    ARRAY_PAIR_CB05 = 3,
} ArrayPairKind;

typedef struct ArrayPairWork {
    uint8_t kind;
    uint8_t reserved[3];
    uint32_t first;
    uint32_t second;
} ArrayPairWork;

/* Static array closure revisits the complete frozen candidate set after each
 * growth round.  Record semantic rule witnesses so a prior round cannot add
 * the same candidate evidence again. */
static bool array_pair_mark_new(GHashTable *processed, uint8_t kind,
                                uint32_t first, uint32_t second)
{
    OspreyKey key;
    memset(&key, 0, sizeof(key));
    key.tag = 0x415250ULL; /* "ARP" */
    key.w[0] = kind;
    key.w[1] = first;
    key.w[2] = second;
    if (g_hash_table_contains(processed, &key)) return false;
    g_hash_table_add(processed, osprey_key_new(&key));
    return true;
}

static int rule_u64_compare(uint64_t a, uint64_t b)
{
    return a < b ? -1 : a != b;
}

static int rule_i64_compare(int64_t a, int64_t b)
{
    return a < b ? -1 : a != b;
}

static int rule_region_compare(const OspreyRegionId *a,
                               const OspreyRegionId *b)
{
    int result = rule_u64_compare((uint64_t)a->kind, (uint64_t)b->kind);
    if (result != 0) return result;
    result = rule_u64_compare(a->code_image_id, b->code_image_id);
    if (result != 0) return result;
    return rule_u64_compare(a->site_offset, b->site_offset);
}

static int rule_address_compare(const OspreyAddress *a,
                                const OspreyAddress *b)
{
    int result = rule_region_compare(&a->region, &b->region);
    return result != 0 ? result : rule_i64_compare(a->offset, b->offset);
}

static int array_id_compare(gconstpointer ap, gconstpointer bp,
                            gpointer user_data)
{
    const OspreyGraph *graph = user_data;
    uint32_t a_id = *(const uint32_t *)ap;
    uint32_t b_id = *(const uint32_t *)bp;
    const OspreyVar *a = &g_array_index(graph->vars, OspreyVar, a_id);
    const OspreyVar *b = &g_array_index(graph->vars, OspreyVar, b_id);
    int result = rule_address_compare(&a->payload.segment.a1,
                                      &b->payload.segment.a1);
    if (result != 0) return result;
    result = rule_address_compare(&a->payload.segment.a2,
                                  &b->payload.segment.a2);
    if (result != 0) return result;
    result = rule_i64_compare(a->payload.segment.size,
                              b->payload.segment.size);
    return result != 0 ? result : rule_u64_compare(a_id, b_id);
}

static int scalar_id_compare(gconstpointer ap, gconstpointer bp,
                             gpointer user_data)
{
    const OspreyGraph *graph = user_data;
    uint32_t a_id = *(const uint32_t *)ap;
    uint32_t b_id = *(const uint32_t *)bp;
    const OspreyVar *a = &g_array_index(graph->vars, OspreyVar, a_id);
    const OspreyVar *b = &g_array_index(graph->vars, OspreyVar, b_id);
    int result = rule_address_compare(&a->payload.chunk.address,
                                      &b->payload.chunk.address);
    if (result != 0) return result;
    result = rule_u64_compare(a->payload.chunk.size,
                              b->payload.chunk.size);
    return result != 0 ? result : rule_u64_compare(a_id, b_id);
}

static GArray *array_ids_snapshot(OspreyContext *ctx)
{
    GArray *ids = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    for (guint i = 0; i < ctx->graph->vars->len; i++) {
        const OspreyVar *variable = &g_array_index(ctx->graph->vars,
                                                   OspreyVar, i);
        if (variable->kind == OSPREY_PRED_ARRAY) {
            uint32_t id = variable->id;
            g_array_append_val(ids, id);
        }
    }
    g_array_sort_with_data(ids, array_id_compare, ctx->graph);
    return ids;
}

static GArray *scalar_ids_snapshot(OspreyContext *ctx)
{
    GArray *ids = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    for (guint i = 0; i < ctx->graph->vars->len; i++) {
        const OspreyVar *variable = &g_array_index(ctx->graph->vars,
                                                   OspreyVar, i);
        if (variable->kind == OSPREY_PRED_SCALAR) {
            uint32_t id = variable->id;
            g_array_append_val(ids, id);
        }
    }
    g_array_sort_with_data(ids, scalar_id_compare, ctx->graph);
    return ids;
}

static bool ordered_array_pair(const OspreyVar *left,
                               const OspreyVar *right,
                               const OspreyVar **first,
                               const OspreyVar **second)
{
    const OspreyAddress *left_lo, *left_hi;
    const OspreyAddress *right_lo, *right_hi;
    int64_t left_stride, right_stride;
    if (!array_interval(left, &left_lo, &left_hi, &left_stride) ||
        !array_interval(right, &right_lo, &right_hi, &right_stride) ||
        !same_region_addr(left_lo, right_lo)) {
        return false;
    }
    if (left_lo->offset > right_lo->offset ||
        (left_lo->offset == right_lo->offset &&
         (left_hi->offset > right_hi->offset ||
          (left_hi->offset == right_hi->offset &&
           left_stride > right_stride)))) {
        const OspreyVar *swap = left;
        left = right;
        right = swap;
        left_lo = &left->payload.segment.a1;
        left_hi = &left->payload.segment.a2;
        right_lo = &right->payload.segment.a1;
        right_hi = &right->payload.segment.a2;
    }
    if (right_lo->offset < left_lo->offset ||
        left_hi->offset < right_lo->offset ||
        right_hi->offset < left_hi->offset) {
        return false;
    }
    *first = left;
    *second = right;
    return true;
}

static OspreyStatus array_pair_work(OspreyContext *ctx,
                                    const OspreyVar *first,
                                    const OspreyVar *second,
                                    GHashTable *processed,
                                    GArray *pairs, GArray *works,
                                    GArray *proposals)
{
    const OspreyAddress *first_lo, *first_hi;
    const OspreyAddress *second_lo, *second_hi;
    int64_t first_stride, second_stride, delta;
    if (!array_interval(first, &first_lo, &first_hi, &first_stride) ||
        !array_interval(second, &second_lo, &second_hi, &second_stride)) {
        return OSPREY_OK;
    }
    if (!osprey_check_sub(second_lo->offset, first_lo->offset, &delta)) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }
    bool compatible = first_stride == second_stride &&
                      delta % first_stride == 0;
    ArrayPairWork pair;
    memset(&pair, 0, sizeof(pair));
    pair.kind = compatible ? ARRAY_PAIR_CB03 : ARRAY_PAIR_CB04;
    pair.first = first->id;
    pair.second = second->id;
    if (!array_pair_mark_new(processed, pair.kind, pair.first, pair.second)) {
        return OSPREY_OK;
    }
    g_array_append_val(pairs, pair);
    if (compatible) {
        OspreyVarPayload union_payload;
        if (!array_payload_make(first_lo, second_hi, first_stride,
                                &union_payload)) {
            return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
        }
        uint32_t existing = rule_var_id(ctx, OSPREY_PRED_ARRAY,
                                        &union_payload);
        if (existing != first->id && existing != second->id) {
            ArrayDerivedWork work;
            memset(&work, 0, sizeof(work));
            work.kind = ARRAY_DERIVED_CB03_UNION;
            work.first = first->id;
            work.second = second->id;
            work.payload = union_payload;
            g_array_append_val(works, work);
            candidate_append(proposals, OSPREY_PRED_ARRAY, &union_payload,
                             1, P_UP, OSPREY_RULE_CB03);
        }
    } else {
        int64_t left_span;
        if (!osprey_check_sub(second_lo->offset, first_lo->offset,
                              &left_span)) {
            return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
        }
        if (left_span >= first_stride) {
            OspreyVarPayload left_payload;
            if (!array_payload_make(first_lo, second_lo, first_stride,
                                    &left_payload)) {
                return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
            }
            uint32_t existing = rule_var_id(ctx, OSPREY_PRED_ARRAY,
                                            &left_payload);
            if (existing != first->id) {
                ArrayDerivedWork work;
                memset(&work, 0, sizeof(work));
                work.kind = ARRAY_DERIVED_CB04_LEFT;
                work.first = first->id;
                work.payload = left_payload;
                g_array_append_val(works, work);
                candidate_append(proposals, OSPREY_PRED_ARRAY, &left_payload,
                                 1, P_UP, OSPREY_RULE_CB04);
            }
        }
        int64_t right_span;
        if (!osprey_check_sub(second_hi->offset, first_hi->offset,
                              &right_span)) {
            return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
        }
        if (right_span >= second_stride) {
            OspreyVarPayload right_payload;
            if (!array_payload_make(first_hi, second_hi, second_stride,
                                    &right_payload)) {
                return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
            }
            uint32_t existing = rule_var_id(ctx, OSPREY_PRED_ARRAY,
                                            &right_payload);
            if (existing != second->id) {
                ArrayDerivedWork work;
                memset(&work, 0, sizeof(work));
                work.kind = ARRAY_DERIVED_CB04_RIGHT;
                work.first = second->id;
                work.payload = right_payload;
                g_array_append_val(works, work);
                candidate_append(proposals, OSPREY_PRED_ARRAY,
                                 &right_payload, 1, P_UP,
                                 OSPREY_RULE_CB04);
            }
        }
    }
    return OSPREY_OK;
}

static OspreyStatus scalar_array_work(OspreyContext *ctx,
                                      const OspreyVar *array,
                                      const OspreyVar *scalar,
                                      GHashTable *processed,
                                      GArray *pairs, GArray *works,
                                      GArray *proposals)
{
    const OspreyAddress *lo, *hi;
    int64_t stride;
    if (!array_interval(array, &lo, &hi, &stride) ||
        !same_region_addr(lo, &scalar->payload.chunk.address)) {
        return OSPREY_OK;
    }
    if (scalar->payload.chunk.size == 0) {
        return rules_error(ctx, OSPREY_INVALID_GRAPH);
    }
    if (scalar->payload.chunk.size > (uint64_t)INT64_MAX) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }
    int64_t scalar_end;
    if (!osprey_check_add(scalar->payload.chunk.address.offset,
                          (int64_t)scalar->payload.chunk.size,
                          &scalar_end)) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }
    int64_t scalar_offset = scalar->payload.chunk.address.offset;
    if (scalar_offset < lo->offset || scalar_offset >= hi->offset) {
        return OSPREY_OK;
    }

    /* The printed CB05 exclusion is Scalar(v) ↔ Array(...). */
    ArrayPairWork pair;
    memset(&pair, 0, sizeof(pair));
    pair.kind = ARRAY_PAIR_CB05;
    pair.first = scalar->id;
    pair.second = array->id;
    if (!array_pair_mark_new(processed, pair.kind, pair.first, pair.second)) {
        return OSPREY_OK;
    }
    g_array_append_val(pairs, pair);

    int64_t left_span;
    if (!osprey_check_sub(scalar_offset, lo->offset, &left_span)) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }
    if (left_span >= stride) {
        OspreyVarPayload left_payload;
        if (!array_payload_make(lo, &scalar->payload.chunk.address, stride,
                                &left_payload)) {
            return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
        }
        ArrayDerivedWork work;
        memset(&work, 0, sizeof(work));
        work.kind = ARRAY_DERIVED_CB05_LEFT;
        work.first = array->id;
        work.second = scalar->id;
        work.payload = left_payload;
        g_array_append_val(works, work);
        candidate_append(proposals, OSPREY_PRED_ARRAY, &left_payload,
                         1, P_UP, OSPREY_RULE_CB05);
    }

    int64_t right_span;
    if (!osprey_check_sub(hi->offset, scalar_end, &right_span)) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }
    if (right_span >= stride) {
        OspreyAddress right_lo = scalar->payload.chunk.address;
        right_lo.offset = scalar_end;
        OspreyVarPayload right_payload;
        if (!array_payload_make(&right_lo, hi, stride, &right_payload)) {
            return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
        }
        ArrayDerivedWork work;
        memset(&work, 0, sizeof(work));
        work.kind = ARRAY_DERIVED_CB05_RIGHT;
        work.first = array->id;
        work.second = scalar->id;
        work.payload = right_payload;
        g_array_append_val(works, work);
        candidate_append(proposals, OSPREY_PRED_ARRAY, &right_payload,
                         1, P_UP, OSPREY_RULE_CB05);
    }
    return OSPREY_OK;
}

static OspreyStatus compile_array_pair_works(OspreyContext *ctx,
                                              const GArray *pairs)
{
    for (guint i = 0; i < pairs->len; i++) {
        const ArrayPairWork *pair = &g_array_index(
            pairs, ArrayPairWork, i);
        uint16_t rule;
        bool negative;
        double probability;
        switch (pair->kind) {
        case ARRAY_PAIR_CB03:
            rule = OSPREY_RULE_CB03;
            negative = false;
            probability = P_UP;
            break;
        case ARRAY_PAIR_CB04:
            rule = OSPREY_RULE_CB04;
            negative = true;
            probability = P_DN;
            break;
        case ARRAY_PAIR_CB05:
            rule = OSPREY_RULE_CB05;
            negative = true;
            probability = P_DN;
            break;
        default:
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        OspreyFactorBatchResult result = osprey_factor_add_bidirectional(
            ctx, rule, OSPREY_GRAPH_SECONDARY, negative, probability,
            pair->first, pair->second);
        if (result.status != OSPREY_OK) return result.status;
    }
    return OSPREY_OK;
}

static OspreyStatus compile_array_derived_works(OspreyContext *ctx,
                                                 const GArray *works)
{
    for (guint i = 0; i < works->len; i++) {
        const ArrayDerivedWork *work = &g_array_index(
            works, ArrayDerivedWork, i);
        uint32_t derived = rule_var_id(ctx, OSPREY_PRED_ARRAY,
                                       &work->payload);
        if (derived == UINT32_MAX) continue;
        OspreyFactorResult result;
        if (work->kind == ARRAY_DERIVED_CB03_UNION) {
            if (derived == work->first || derived == work->second) continue;
            uint32_t antecedents[2] = { work->first, work->second };
            result = osprey_factor_add_implication(
                ctx, OSPREY_RULE_CB03, OSPREY_GRAPH_SECONDARY, false, P_UP,
                antecedents, G_N_ELEMENTS(antecedents), derived);
        } else if (work->kind == ARRAY_DERIVED_CB04_LEFT ||
                   work->kind == ARRAY_DERIVED_CB04_RIGHT) {
            if (derived == work->first) continue;
            result = osprey_factor_add_implication(
                ctx, OSPREY_RULE_CB04, OSPREY_GRAPH_SECONDARY, false, P_UP,
                &work->first, 1, derived);
        } else {
            if (derived == work->first || derived == work->second) continue;
            uint32_t antecedents[2] = { work->first, work->second };
            result = osprey_factor_add_implication(
                ctx, OSPREY_RULE_CB05, OSPREY_GRAPH_SECONDARY, false, P_UP,
                antecedents, G_N_ELEMENTS(antecedents), derived);
        }
        if (result.status != OSPREY_OK) return result.status;
    }
    return OSPREY_OK;
}

/* One round consumes a frozen array/scalar ID set.  Candidate selection is
 * performed only after all pair witnesses are collected, so cap outcomes do
 * not depend on GArray mutation or witness order. */
static OspreyStatus secondary_array_round(OspreyContext *ctx,
                                           GHashTable *processed,
                                           bool *changed)
{
    guint vars_before = ctx->graph->vars->len;
    guint factors_before = ctx->graph->factors->len;
    GArray *arrays = array_ids_snapshot(ctx);
    GArray *scalars = scalar_ids_snapshot(ctx);
    GArray *pairs = g_array_new(FALSE, FALSE, sizeof(ArrayPairWork));
    GArray *works = g_array_new(FALSE, FALSE, sizeof(ArrayDerivedWork));
    GArray *proposals = g_array_new(FALSE, FALSE,
                                    sizeof(OspreyCandidateProposal));
    OspreyStatus status = OSPREY_OK;

    for (guint i = 0; i < arrays->len && status == OSPREY_OK; i++) {
        uint32_t first_id = g_array_index(arrays, uint32_t, i);
        const OspreyVar *first = &g_array_index(ctx->graph->vars,
                                                OspreyVar, first_id);
        for (guint j = i + 1; j < arrays->len; j++) {
            uint32_t second_id = g_array_index(arrays, uint32_t, j);
            const OspreyVar *second = &g_array_index(ctx->graph->vars,
                                                     OspreyVar, second_id);
            const OspreyVar *ordered_first, *ordered_second;
            if (!ordered_array_pair(first, second, &ordered_first,
                                    &ordered_second)) {
                continue;
            }
            status = array_pair_work(ctx, ordered_first, ordered_second,
                                     processed, pairs, works, proposals);
            if (status != OSPREY_OK) break;
        }
    }
    for (guint i = 0; i < arrays->len && status == OSPREY_OK; i++) {
        uint32_t array_id = g_array_index(arrays, uint32_t, i);
        const OspreyVar *array = &g_array_index(ctx->graph->vars,
                                                OspreyVar, array_id);
        for (guint j = 0; j < scalars->len; j++) {
            uint32_t scalar_id = g_array_index(scalars, uint32_t, j);
            const OspreyVar *scalar = &g_array_index(ctx->graph->vars,
                                                     OspreyVar, scalar_id);
            status = scalar_array_work(ctx, array, scalar, processed,
                                       pairs, works, proposals);
            if (status != OSPREY_OK) break;
        }
    }

    if (status == OSPREY_OK && proposals->len != 0) {
        status = select_new_candidates(ctx, proposals);
    }
    if (status == OSPREY_OK) {
        status = compile_array_pair_works(ctx, pairs);
    }
    if (status == OSPREY_OK) {
        status = compile_array_derived_works(ctx, works);
    }
    *changed = ctx->graph->vars->len != vars_before ||
               ctx->graph->factors->len != factors_before;
    g_array_free(proposals, TRUE);
    g_array_free(works, TRUE);
    g_array_free(pairs, TRUE);
    g_array_free(scalars, TRUE);
    g_array_free(arrays, TRUE);
    return status;
}

/* CC04/CC05: distinct unfoldable prefixes at one site are mutually
 * exclusive, while the smaller prefix supports the larger one. */
static OspreyStatus compile_cc04_cc05(OspreyContext *ctx)
{
    OspreyGraph *graph = ctx->graph;
    for (guint i = 0; i < graph->vars->len; i++) {
        const OspreyVar *first = &g_array_index(graph->vars, OspreyVar, i);
        if (first->kind != OSPREY_PRED_UNFOLDABLE_HEAP) continue;
        for (guint j = i + 1; j < graph->vars->len; j++) {
            const OspreyVar *second = &g_array_index(graph->vars,
                                                     OspreyVar, j);
            if (second->kind != OSPREY_PRED_UNFOLDABLE_HEAP ||
                !same_region(&first->payload.heap_fold.region,
                             &second->payload.heap_fold.region) ||
                first->payload.heap_fold.size ==
                    second->payload.heap_fold.size) {
                continue;
            }
            const OspreyVar *small = first;
            const OspreyVar *large = second;
            if (small->payload.heap_fold.size > large->payload.heap_fold.size) {
                small = second;
                large = first;
            }
            OspreyFactorBatchResult exclusion = osprey_factor_add_bidirectional(
                ctx, OSPREY_RULE_CC04, OSPREY_GRAPH_SECONDARY, true, P_DN,
                first->id, second->id);
            if (exclusion.status != OSPREY_OK) return exclusion.status;
            OspreyFactorResult support = osprey_factor_add_implication(
                ctx, OSPREY_RULE_CC05, OSPREY_GRAPH_SECONDARY, false, P_UP,
                &small->id, 1, large->id);
            if (support.status != OSPREY_OK) return support.status;
        }
    }
    return OSPREY_OK;
}

static bool rules_extent_contains(const OspreyGraph *graph,
                                  const OspreyRegionId *region,
                                  int64_t lo, int64_t hi);

/* CC06: an array in a heap site supports the site's fold unit. */
static OspreyStatus collect_cc06(OspreyContext *ctx, GArray *proposals)
{
    OspreyGraph *graph = ctx->graph;
    for (guint i = 0; i < graph->vars->len; i++) {
        const OspreyVar *array = &g_array_index(graph->vars, OspreyVar, i);
        if (array->kind != OSPREY_PRED_ARRAY ||
            array->payload.segment.a1.region.kind !=
                OSPREY_REGION_HEAP_SITE ||
            !same_region_addr(&array->payload.segment.a1,
                               &array->payload.segment.a2) ||
            array->payload.segment.size <= 0) {
            continue;
        }
        int64_t span;
        if (!osprey_check_sub(array->payload.segment.a2.offset,
                              array->payload.segment.a1.offset, &span)) {
            return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
        }
        if (span < array->payload.segment.size) continue;
        if (!rules_extent_contains(graph,
                                   &array->payload.segment.a1.region,
                                   array->payload.segment.a1.offset,
                                   array->payload.segment.a2.offset)) {
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        OspreyVarPayload foldable;
        memset(&foldable, 0, sizeof(foldable));
        foldable.heap_fold.region = array->payload.segment.a1.region;
        foldable.heap_fold.size = (uint64_t)array->payload.segment.size;
        candidate_append(proposals, OSPREY_PRED_FOLDABLE_HEAP, &foldable,
                         1, P_UP, OSPREY_RULE_CC06);
    }
    return OSPREY_OK;
}

static OspreyStatus compile_cc06(OspreyContext *ctx)
{
    OspreyGraph *graph = ctx->graph;
    for (guint i = 0; i < graph->vars->len; i++) {
        const OspreyVar *array = &g_array_index(graph->vars, OspreyVar, i);
        if (array->kind != OSPREY_PRED_ARRAY ||
            array->payload.segment.a1.region.kind !=
                OSPREY_REGION_HEAP_SITE ||
            array->payload.segment.size <= 0 ||
            !same_region_addr(&array->payload.segment.a1,
                               &array->payload.segment.a2)) {
            continue;
        }
        OspreyVarPayload foldable;
        memset(&foldable, 0, sizeof(foldable));
        foldable.heap_fold.region = array->payload.segment.a1.region;
        foldable.heap_fold.size = (uint64_t)array->payload.segment.size;
        uint32_t foldable_id = rule_var_id(ctx, OSPREY_PRED_FOLDABLE_HEAP,
                                           &foldable);
        if (foldable_id == UINT32_MAX) {
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        OspreyFactorResult result = osprey_factor_add_implication(
            ctx, OSPREY_RULE_CC06, OSPREY_GRAPH_SECONDARY, false, P_UP,
            &array->id, 1, foldable_id);
        if (result.status != OSPREY_OK) return result.status;
    }
    return OSPREY_OK;
}

static bool rules_extent_contains(const OspreyGraph *graph,
                                  const OspreyRegionId *region,
                                  int64_t lo, int64_t hi)
{
    if (graph == NULL || region == NULL || !graph->extents_built || lo > hi) {
        return false;
    }
    for (guint i = 0; i < graph->extents->len; i++) {
        const OspreyRegionExtent *extent = &g_array_index(
            graph->extents, OspreyRegionExtent, i);
        if (same_region(&extent->region, region)) {
            return lo >= extent->lo && hi <= extent->hi;
        }
    }
    return false;
}

/* Pure CC07 compiler.  Stage 3 does not schedule this rule from beliefs;
 * Stage 5 supplies explicit selected candidate IDs to this entrypoint. */
OspreyStatus osprey_compile_cc07(OspreyContext *ctx,
                                 uint32_t primitive_id,
                                 uint32_t unfoldable_id,
                                 uint32_t foldable_id,
                                 uint32_t folded_primitive_id)
{
    if (ctx == NULL || ctx->graph == NULL ||
        primitive_id >= ctx->graph->vars->len ||
        unfoldable_id >= ctx->graph->vars->len ||
        foldable_id >= ctx->graph->vars->len ||
        folded_primitive_id >= ctx->graph->vars->len) {
        return rules_error(ctx, OSPREY_INVALID_GRAPH);
    }
    OspreyGraph *graph = ctx->graph;
    const OspreyVar *primitive = &g_array_index(graph->vars, OspreyVar,
                                                primitive_id);
    const OspreyVar *unfoldable = &g_array_index(graph->vars, OspreyVar,
                                                  unfoldable_id);
    const OspreyVar *foldable = &g_array_index(graph->vars, OspreyVar,
                                                foldable_id);
    const OspreyVar *folded = &g_array_index(graph->vars, OspreyVar,
                                             folded_primitive_id);
    if (primitive->kind != OSPREY_PRED_PRIMITIVE_VAR ||
        unfoldable->kind != OSPREY_PRED_UNFOLDABLE_HEAP ||
        foldable->kind != OSPREY_PRED_FOLDABLE_HEAP ||
        folded->kind != OSPREY_PRED_PRIMITIVE_VAR ||
        primitive->payload.chunk.address.region.kind !=
            OSPREY_REGION_HEAP_SITE ||
        !same_region(&primitive->payload.chunk.address.region,
                     &unfoldable->payload.heap_fold.region) ||
        !same_region(&primitive->payload.chunk.address.region,
                     &foldable->payload.heap_fold.region) ||
        !same_region(&primitive->payload.chunk.address.region,
                     &folded->payload.chunk.address.region)) {
        return rules_error(ctx, OSPREY_INVALID_GRAPH);
    }
    if (primitive->payload.chunk.size > (uint64_t)INT64_MAX ||
        unfoldable->payload.heap_fold.size > (uint64_t)INT64_MAX ||
        foldable->payload.heap_fold.size > (uint64_t)INT64_MAX) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }
    if (foldable->payload.heap_fold.size == 0) {
        return rules_error(ctx, OSPREY_INVALID_GRAPH);
    }
    int64_t sh = (int64_t)unfoldable->payload.heap_fold.size;
    int64_t st = (int64_t)foldable->payload.heap_fold.size;
    int64_t threshold;
    if (!osprey_check_add(sh, st, &threshold)) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }
    int64_t relative;
    if (!osprey_check_sub(primitive->payload.chunk.address.offset, sh,
                          &relative)) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }
    if (primitive->payload.chunk.address.offset < threshold || relative < 0) {
        return rules_error(ctx, OSPREY_INVALID_GRAPH);
    }
    int64_t folded_offset;
    if (!osprey_check_add(sh, relative % st, &folded_offset)) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }
    int64_t primitive_end;
    int64_t folded_end;
    if (!osprey_check_add(primitive->payload.chunk.address.offset,
                          (int64_t)primitive->payload.chunk.size,
                          &primitive_end) ||
        !osprey_check_add(folded_offset,
                          (int64_t)primitive->payload.chunk.size,
                          &folded_end)) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }
    const OspreyRegionId *heap = &primitive->payload.chunk.address.region;
    if (!rules_extent_contains(graph, heap,
                               primitive->payload.chunk.address.offset,
                               primitive_end) ||
        !rules_extent_contains(graph, heap, folded_offset, folded_end) ||
        !rules_extent_contains(graph, heap, 0, sh) ||
        !rules_extent_contains(graph, heap, 0, st)) {
        return rules_error(ctx, OSPREY_INVALID_GRAPH);
    }
    OspreyChunk expected = primitive->payload.chunk;
    expected.address.offset = folded_offset;
    if (!chunk_equal(&expected, &folded->payload.chunk) ||
        folded_primitive_id == primitive_id) {
        return rules_error(ctx, OSPREY_INVALID_GRAPH);
    }
    uint32_t folded_ids[3] = { primitive_id, unfoldable_id, foldable_id };
    OspreyFactorResult result = osprey_factor_add_implication(
        ctx, OSPREY_RULE_CC07, OSPREY_GRAPH_SECONDARY, false, P_UP,
        folded_ids, G_N_ELEMENTS(folded_ids), folded_primitive_id);
    if (result.status != OSPREY_OK) return result.status;
    uint32_t negative_ids[2] = { unfoldable_id, foldable_id };
    result = osprey_factor_add_implication(
        ctx, OSPREY_RULE_CC07, OSPREY_GRAPH_SECONDARY, true, P_DN,
        negative_ids, 2, primitive_id);
    return result.status;
}

/* CD07: PrimitiveVar(v) in heap H_i -> FieldOf(v, <H_i,0>). */
static OspreyStatus collect_cd07(OspreyContext *ctx, GArray *proposals)
{
    OspreyGraph *graph = ctx->graph;
    for (guint i = 0; i < graph->vars->len; i++) {
        const OspreyVar *primitive = &g_array_index(graph->vars,
                                                    OspreyVar, i);
        if (primitive->kind != OSPREY_PRED_PRIMITIVE_VAR ||
            primitive->payload.chunk.address.region.kind !=
                OSPREY_REGION_HEAP_SITE) {
            continue;
        }
        OspreyVarPayload field;
        memset(&field, 0, sizeof(field));
        field.attached.chunk = primitive->payload.chunk;
        field.attached.base.region = primitive->payload.chunk.address.region;
        field.attached.base.offset = 0;
        candidate_append(proposals, OSPREY_PRED_FIELD_OF, &field,
                         primitive->direct_support, P_UP,
                         OSPREY_RULE_CD07);
    }
    return OSPREY_OK;
}

static OspreyStatus compile_cd07(OspreyContext *ctx)
{
    OspreyGraph *graph = ctx->graph;
    for (guint i = 0; i < graph->vars->len; i++) {
        const OspreyVar *primitive = &g_array_index(graph->vars,
                                                    OspreyVar, i);
        if (primitive->kind != OSPREY_PRED_PRIMITIVE_VAR ||
            primitive->payload.chunk.address.region.kind !=
                OSPREY_REGION_HEAP_SITE) {
            continue;
        }
        OspreyVarPayload field;
        memset(&field, 0, sizeof(field));
        field.attached.chunk = primitive->payload.chunk;
        field.attached.base.region = primitive->payload.chunk.address.region;
        field.attached.base.offset = 0;
        uint32_t field_id = rule_var_id(ctx, OSPREY_PRED_FIELD_OF, &field);
        if (field_id == UINT32_MAX) {
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        OspreyFactorResult result = osprey_factor_add_implication(
            ctx, OSPREY_RULE_CD07, OSPREY_GRAPH_SECONDARY, false, P_UP,
            &primitive->id, 1, field_id);
        if (result.status != OSPREY_OK) return result.status;
    }
    return OSPREY_OK;
}

typedef struct Cd08WorkKey {
    uint32_t field_id;
    uint32_t homo_id;
    OspreyVarPayload payload;
} Cd08WorkKey;

typedef struct Cd08Work {
    uint32_t field_id;
    uint32_t homo_id;
    OspreyVarPayload payload;
} Cd08Work;

/* CD08: translate complete, equal-width accessed fields across each
 * endpoint direction of every selected HomoSegment. */
static OspreyStatus cd08_round(OspreyContext *ctx, GHashTable *seen,
                               bool *changed)
{
    OspreyGraph *graph = ctx->graph;
    guint vars_before = graph->vars->len;
    guint factors_before = graph->factors->len;
    GArray *homos = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    GArray *fields = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    GArray *works = g_array_new(FALSE, FALSE, sizeof(Cd08Work));
    GArray *proposals = g_array_new(FALSE, FALSE,
                                    sizeof(OspreyCandidateProposal));
    for (guint i = 0; i < graph->vars->len; i++) {
        const OspreyVar *variable = &g_array_index(graph->vars,
                                                   OspreyVar, i);
        if (variable->kind == OSPREY_PRED_HOMO_SEGMENT) {
            uint32_t id = variable->id;
            g_array_append_val(homos, id);
        } else if (variable->kind == OSPREY_PRED_FIELD_OF) {
            uint32_t id = variable->id;
            g_array_append_val(fields, id);
        }
    }

    OspreyStatus status = OSPREY_OK;
    for (guint hi = 0; hi < homos->len && status == OSPREY_OK; hi++) {
        uint32_t homo_id = g_array_index(homos, uint32_t, hi);
        const OspreyVar *homo = &g_array_index(graph->vars, OspreyVar,
                                                homo_id);
        if (homo->payload.segment.size <= 0) {
            status = rules_error(ctx, OSPREY_INVALID_GRAPH);
            break;
        }
        for (unsigned direction = 0; direction < 2 &&
             status == OSPREY_OK; direction++) {
            const OspreyAddress *from = direction == 0
                ? &homo->payload.segment.a1 : &homo->payload.segment.a2;
            const OspreyAddress *to = direction == 0
                ? &homo->payload.segment.a2 : &homo->payload.segment.a1;
            int64_t segment_end;
            if (!osprey_check_add(from->offset,
                                  homo->payload.segment.size,
                                  &segment_end)) {
                status = rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
                break;
            }
            for (guint fi = 0; fi < fields->len && status == OSPREY_OK;
                 fi++) {
                uint32_t field_id = g_array_index(fields, uint32_t, fi);
                const OspreyVar *field = &g_array_index(
                    graph->vars, OspreyVar, field_id);
                const OspreyChunk *source = &field->payload.attached.chunk;
                if (!address_equal(&field->payload.attached.base, from) ||
                    !same_region(&source->address.region, &from->region)) {
                    continue;
                }
                if (source->size > (uint64_t)INT64_MAX) {
                    status = rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
                    break;
                }
                int64_t relative;
                if (!osprey_check_sub(source->address.offset, from->offset,
                                      &relative)) {
                    status = rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
                    break;
                }
                int64_t source_end;
                if (!osprey_check_add(source->address.offset,
                                      (int64_t)source->size, &source_end)) {
                    status = rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
                    break;
                }
                if (relative < 0 || relative >= homo->payload.segment.size ||
                    source_end > segment_end) {
                    continue;
                }
                int64_t target_offset;
                if (!osprey_check_add(to->offset, relative,
                                      &target_offset)) {
                    status = rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
                    break;
                }
                for (guint ai = 0; ai < ctx->relations->r02_accessed->len;
                     ai++) {
                    const OspreyChunkRelation *access = &g_array_index(
                        ctx->relations->r02_accessed,
                        OspreyChunkRelation, ai);
                    if (!same_region(&access->chunk.address.region,
                                     &to->region) ||
                        access->chunk.address.offset != target_offset ||
                        access->chunk.size != source->size) {
                        continue;
                    }
                    int64_t target_end;
                    if (access->chunk.size > (uint64_t)INT64_MAX ||
                        !osprey_check_add(target_offset,
                                          (int64_t)access->chunk.size,
                                          &target_end)) {
                        status = rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
                        break;
                    }
                    int64_t target_segment_end;
                    if (!osprey_check_add(to->offset,
                                          homo->payload.segment.size,
                                          &target_segment_end)) {
                        status = rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
                        break;
                    }
                    if (target_end > target_segment_end) continue;
                    OspreyVarPayload payload;
                    memset(&payload, 0, sizeof(payload));
                    payload.attached.chunk = access->chunk;
                    payload.attached.base = *to;
                    Cd08WorkKey key;
                    memset(&key, 0, sizeof(key));
                    key.field_id = field_id;
                    key.homo_id = homo_id;
                    key.payload = payload;
                    if (!rule_witness_mark(seen, &key, sizeof(key))) {
                        continue;
                    }
                    uint32_t existing = rule_var_id(
                        ctx, OSPREY_PRED_FIELD_OF, &payload);
                    if (existing == field_id) continue;
                    Cd08Work work;
                    memset(&work, 0, sizeof(work));
                    work.field_id = field_id;
                    work.homo_id = homo_id;
                    work.payload = payload;
                    g_array_append_val(works, work);
                    candidate_append(proposals, OSPREY_PRED_FIELD_OF,
                                     &payload, 1, P_UP, OSPREY_RULE_CD08);
                }
            }
        }
    }
    if (status == OSPREY_OK && proposals->len != 0) {
        status = select_new_candidates(ctx, proposals);
    }
    for (guint i = 0; i < works->len && status == OSPREY_OK; i++) {
        const Cd08Work *work = &g_array_index(works, Cd08Work, i);
        uint32_t target = rule_var_id(ctx, OSPREY_PRED_FIELD_OF,
                                      &work->payload);
        if (target == UINT32_MAX) {
            status = rules_error(ctx, OSPREY_INVALID_GRAPH);
            break;
        }
        if (target == work->field_id) continue;
        uint32_t ids[2] = { work->field_id, work->homo_id };
        OspreyFactorResult result = osprey_factor_add_implication(
            ctx, OSPREY_RULE_CD08, OSPREY_GRAPH_SECONDARY, false, P_UP,
            ids, G_N_ELEMENTS(ids), target);
        if (result.status != OSPREY_OK) status = result.status;
    }
    *changed = graph->vars->len != vars_before ||
               graph->factors->len != factors_before;
    g_array_free(proposals, TRUE);
    g_array_free(works, TRUE);
    g_array_free(fields, TRUE);
    g_array_free(homos, TRUE);
    return status;
}

/* CD05: corresponding primitive chunks of unequal width disfavor their
 * common HomoSegment.  Field spans, not just starts, must fit each segment. */
static OspreyStatus compile_cd05(OspreyContext *ctx)
{
    OspreyGraph *graph = ctx->graph;
    for (guint hi = 0; hi < graph->vars->len; hi++) {
        const OspreyVar *homo = &g_array_index(graph->vars, OspreyVar, hi);
        if (homo->kind != OSPREY_PRED_HOMO_SEGMENT ||
            homo->payload.segment.size <= 0) {
            continue;
        }
        const OspreyAddress *from = &homo->payload.segment.a1;
        const OspreyAddress *to = &homo->payload.segment.a2;
        int64_t from_end;
        int64_t to_end;
        if (!osprey_check_add(from->offset,
                              homo->payload.segment.size, &from_end) ||
            !osprey_check_add(to->offset,
                              homo->payload.segment.size, &to_end)) {
            return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
        }
        for (guint i = 0; i < graph->vars->len; i++) {
            const OspreyVar *left = &g_array_index(graph->vars,
                                                   OspreyVar, i);
            if (left->kind != OSPREY_PRED_PRIMITIVE_VAR ||
                !same_region_addr(&left->payload.chunk.address, from)) {
                continue;
            }
            if (left->payload.chunk.size > (uint64_t)INT64_MAX) {
                return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
            }
            int64_t left_offset;
            int64_t left_end;
            if (!osprey_check_sub(left->payload.chunk.address.offset,
                                  from->offset, &left_offset) ||
                !osprey_check_add(left->payload.chunk.address.offset,
                                  (int64_t)left->payload.chunk.size,
                                  &left_end)) {
                return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
            }
            if (left_offset <= 0 ||
                left_offset >= homo->payload.segment.size ||
                left_end > from_end) {
                continue;
            }
            for (guint j = 0; j < graph->vars->len; j++) {
                const OspreyVar *right = &g_array_index(graph->vars,
                                                        OspreyVar, j);
                if (right->kind != OSPREY_PRED_PRIMITIVE_VAR ||
                    right->payload.chunk.size == left->payload.chunk.size ||
                    right->payload.chunk.size > (uint64_t)INT64_MAX ||
                    !same_region_addr(&right->payload.chunk.address, to)) {
                    continue;
                }
                int64_t right_offset;
                int64_t right_end;
                if (!osprey_check_sub(right->payload.chunk.address.offset,
                                      to->offset, &right_offset) ||
                    !osprey_check_add(right->payload.chunk.address.offset,
                                      (int64_t)right->payload.chunk.size,
                                      &right_end)) {
                    return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
                }
                if (right_offset != left_offset ||
                    right_offset <= 0 ||
                    right_offset >= homo->payload.segment.size ||
                    right_end > to_end) {
                    continue;
                }
                uint32_t antecedents[2] = { left->id, right->id };
                OspreyFactorBatchResult result =
                    osprey_factor_add_conjunction_bidirectional(
                        ctx, OSPREY_RULE_CD05, OSPREY_GRAPH_SECONDARY,
                        true, P_DN, antecedents,
                        G_N_ELEMENTS(antecedents), homo->id);
                if (result.status != OSPREY_OK) return result.status;
            }
        }
    }
    return OSPREY_OK;
}

/* CB06: retain a defensive hard-false factor for an injected malformed
 * array.  Normal production candidates are rejected before interning. */
static OspreyStatus cb06_hard_false(OspreyContext *ctx)
{
    OspreyGraph *graph = ctx->graph;
    for (guint i = 0; i < graph->vars->len; i++) {
        OspreyVar *variable = &g_array_index(graph->vars, OspreyVar, i);
        if (variable->kind != OSPREY_PRED_ARRAY) continue;
        int64_t span;
        int64_t stride = variable->payload.segment.size;
        if (stride <= 0 ||
            !same_region_addr(&variable->payload.segment.a1,
                              &variable->payload.segment.a2)) {
            return rules_error(ctx, OSPREY_INVALID_GRAPH);
        }
        if (!osprey_check_sub(variable->payload.segment.a2.offset,
                              variable->payload.segment.a1.offset, &span)) {
            return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
        }
        if (span < stride) {
            variable->hard_false = 1;
            OspreyFactorResult result = osprey_factor_add_hard_false(
                ctx, OSPREY_RULE_CB06, OSPREY_GRAPH_SECONDARY, variable->id);
            if (result.status != OSPREY_OK) return result.status;
        }
    }
    return OSPREY_OK;
}

static OspreyStatus collect_stage34_direct(OspreyContext *ctx,
                                            GArray *proposals)
{
    OspreyStatus status = collect_cc01_cc02(ctx, proposals);
    if (status != OSPREY_OK) return status;
    status = collect_cc03(ctx, proposals);
    if (status != OSPREY_OK) return status;
    status = collect_cd01_03(ctx, proposals);
    if (status != OSPREY_OK) return status;
    status = collect_cd06(ctx, proposals);
    if (status != OSPREY_OK) return status;
    status = collect_cd11(ctx, proposals);
    if (status != OSPREY_OK) return status;
    return collect_cd07(ctx, proposals);
}

static OspreyStatus compile_stage34_direct(OspreyContext *ctx)
{
    OspreyStatus status = compile_cc01_cc02(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_cc03(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_cd01_03(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_cd06(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_cd11(ctx);
    if (status != OSPREY_OK) return status;
    return compile_cd07(ctx);
}

/* One idempotent replay of every fact/candidate-driven secondary
 * consequence.  CC07 remains deliberately outside this package. */
OspreyStatus osprey_secondary_static_closure(OspreyContext *ctx,
                                             OspreyGraphDelta *delta,
                                             bool emit_stage3_summary)
{
    uint64_t vars_before;
    uint64_t factors_before;
    uint64_t limit_rows_before;

    if (delta != NULL) memset(delta, 0, sizeof(*delta));
    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    if (ctx->graph == NULL || ctx->relations == NULL) {
        return OSPREY_INCOMPLETE_FACTS;
    }
    vars_before = ctx->graph->vars->len;
    factors_before = ctx->graph->factors->len;
    limit_rows_before = ctx->graph->limit_rows;
    osprey_graph_set_stage(ctx->graph, OSPREY_GRAPH_SECONDARY);

    GHashTable *array_processed = g_hash_table_new_full(
        osprey_key_hash, osprey_key_equal, osprey_key_free, NULL);
    OspreyStatus status = OSPREY_OK;
    for (;;) {
        bool changed = false;
        status = secondary_array_round(ctx, array_processed, &changed);
        if (status != OSPREY_OK || !changed) break;
    }
    g_hash_table_destroy(array_processed);
    if (status != OSPREY_OK) return status;

    status = compile_cb09(ctx);
    if (status != OSPREY_OK) return status;

    /* Collect all direct Stage 3.4 candidates only after the base stage has
     * interned PrimitiveVar/PrimitiveAccess candidates.  This is required
     * for CC03, CD06, CD07, and CD11 to consume the complete base set. */
    GArray *secondary_proposals = g_array_new(
        FALSE, FALSE, sizeof(OspreyCandidateProposal));
    status = collect_cc06(ctx, secondary_proposals);
    if (status == OSPREY_OK) {
        status = collect_stage34_direct(ctx, secondary_proposals);
    }
    if (status == OSPREY_OK && secondary_proposals->len != 0) {
        status = select_new_candidates(ctx, secondary_proposals);
    }
    g_array_free(secondary_proposals, TRUE);
    if (status != OSPREY_OK) return status;

    status = compile_stage34_direct(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_cc06(ctx);
    if (status != OSPREY_OK) return status;

    status = compile_cc04_cc05(ctx);
    if (status != OSPREY_OK) return status;

    GHashTable *cd04_pairs = g_hash_table_new_full(
        g_bytes_hash, g_bytes_equal, (GDestroyNotify)g_bytes_unref, NULL);
    GHashTable *cd04_unions = g_hash_table_new_full(
        g_bytes_hash, g_bytes_equal, (GDestroyNotify)g_bytes_unref, NULL);
    for (;;) {
        bool changed = false;
        status = cd04_round(ctx, cd04_pairs, cd04_unions, &changed);
        if (status != OSPREY_OK || !changed) break;
    }
    g_hash_table_destroy(cd04_unions);
    g_hash_table_destroy(cd04_pairs);
    if (status != OSPREY_OK) return status;

    GHashTable *cd08_seen = g_hash_table_new_full(
        g_bytes_hash, g_bytes_equal, (GDestroyNotify)g_bytes_unref, NULL);
    for (;;) {
        bool changed = false;
        status = cd08_round(ctx, cd08_seen, &changed);
        if (status != OSPREY_OK || !changed) break;
    }
    g_hash_table_destroy(cd08_seen);
    if (status != OSPREY_OK) return status;

    status = compile_cd05(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_ca08(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_cd10(ctx);
    if (status != OSPREY_OK) return status;
    status = cb06_hard_false(ctx);
    if (status != OSPREY_OK) return status;

    if (ctx->last_status != OSPREY_OK && ctx->last_status != OSPREY_DISABLED) {
        return ctx->last_status;
    }
    OspreyGraph *graph = ctx->graph;
    uint64_t vars_after = graph->vars->len;
    uint64_t factors_after = graph->factors->len;
    uint64_t limit_rows_after = graph->limit_rows;
    if (vars_after < vars_before || factors_after < factors_before ||
        limit_rows_after < limit_rows_before ||
        vars_after - vars_before > UINT32_MAX ||
        factors_after - factors_before > UINT32_MAX ||
        limit_rows_after - limit_rows_before > UINT32_MAX) {
        return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
    }
    if (delta != NULL) {
        delta->variables_added = (uint32_t)(vars_after - vars_before);
        delta->factors_added = (uint32_t)(factors_after - factors_before);
        delta->limit_rows_added =
            (uint32_t)(limit_rows_after - limit_rows_before);
        for (uint64_t i = factors_before; i < factors_after; i++) {
            const OspreyFactor *factor = g_array_index(
                graph->factors, OspreyFactor *, (guint)i);
            if (factor == NULL) {
                if (delta != NULL) memset(delta, 0, sizeof(*delta));
                return rules_error(ctx, OSPREY_INVALID_GRAPH);
            }
            if (factor->rule >= OSPREY_RULE_CA01 &&
                factor->rule <= OSPREY_RULE_CA08) {
                if (delta->base_factors_added == UINT32_MAX) {
                    if (delta != NULL) memset(delta, 0, sizeof(*delta));
                    return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
                }
                delta->base_factors_added++;
            } else {
                if (delta->secondary_factors_added == UINT32_MAX) {
                    if (delta != NULL) memset(delta, 0, sizeof(*delta));
                    return rules_error(ctx, OSPREY_GRAPH_ARITHMETIC);
                }
                delta->secondary_factors_added++;
            }
        }
    }
    if (emit_stage3_summary) {
        log_msg("[osprey] [graph] [stage secondary] [vars %u] [factors %u]\n",
                graph->vars->len, graph->factors->len);
    }
    return OSPREY_OK;
}

/* Stage-3 secondary entry.  Stage 5 reuses the same compiler without the
 * summary row or a second rule implementation. */
OspreyStatus osprey_stage3_secondary(OspreyContext *ctx)
{
    OspreyGraphDelta delta;
    return osprey_secondary_static_closure(ctx, &delta, true);
}

/* ------------------------------------------------------------------ */
/* Stage-3 base entry                                                  */
/* ------------------------------------------------------------------ */

OspreyStatus osprey_stage3_base(OspreyContext *ctx)
{
    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    if (ctx->total_samples == 0) {
        return rules_error(ctx, OSPREY_INVALID_GRAPH);
    }
    if (ctx->relations == NULL) {
        OspreyStatus relation_status = osprey_relations_build(ctx);
        if (relation_status != OSPREY_OK) {
            osprey_tx_reject(ctx, relation_status, "relations",
                             "checked relation arithmetic failed");
            return relation_status;
        }
    }
    if (ctx->graph == NULL) ctx->graph = osprey_graph_new();
    OspreyGraph *graph = ctx->graph;
    osprey_graph_set_stage(graph, OSPREY_GRAPH_BASE_CA);

    closure_r10(ctx);
    closure_r11(ctx);
    closure_r12(ctx);

    GArray *proposals = g_array_new(FALSE, FALSE,
                                    sizeof(OspreyCandidateProposal));
    OspreyStatus status = collect_initial_ca_cb(ctx, proposals);
    if (status == OSPREY_OK) {
        status = osprey_candidate_select(
            ctx, (const OspreyCandidateProposal *)proposals->data,
            proposals->len);
    }
    g_array_free(proposals, TRUE);
    if (status != OSPREY_OK) return status;

    status = compile_initial_ca_cb(ctx);
    if (status != OSPREY_OK) return status;
    status = compile_ca08(ctx);
    if (status != OSPREY_OK) return status;

    uint32_t components = osprey_graph_component_count(graph);
    if (ctx->last_status != OSPREY_OK && ctx->last_status != OSPREY_DISABLED) {
        return ctx->last_status;
    }
    log_msg("[osprey] [graph] [stage base] [vars %u] [factors %u] "
            "[components %u] [hints %llu] [cd04 %llu]\n",
            graph->vars->len, graph->factors->len, components,
            (unsigned long long)graph->hint_instances,
            (unsigned long long)graph->cd04_extensions);
    return OSPREY_OK;
}

OspreyStatus osprey_stage3_build(OspreyContext *ctx)
{
    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    if (ctx->relations == NULL) {
        OspreyStatus status = osprey_relations_build(ctx);
        if (status != OSPREY_OK) return status;
    }
    OspreyStatus status = osprey_stage3_base(ctx);
    if (status != OSPREY_OK) return status;
    return osprey_stage3_secondary(ctx);
}
