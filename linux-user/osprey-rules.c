/*
 * OSPREY deterministic closure (R01-R12), predicate interning, bounded
 * candidate generation, and static factor instantiation (Stage 2).
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
 *    p_s = p_up scaled by normalized hint-instance support.
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

static int64_t gcd_i64(int64_t a, int64_t b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static void insertion_sort_i64(GArray *a) {
    for (guint i = 1; i < a->len; i++) {
        int64_t v = g_array_index(a, int64_t, i);
        guint j = i;
        while (j > 0 && g_array_index(a, int64_t, j - 1) > v) {
            g_array_index(a, int64_t, j) = g_array_index(a, int64_t, j - 1);
            j--;
        }
        g_array_index(a, int64_t, j) = v;
    }
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
/* Per-(kind,region) candidate limits                                  */
/* ------------------------------------------------------------------ */

static void kr_account(OspreyContext *ctx, uint8_t kind,
                       const OspreyRegionId *region, uint64_t kept,
                       uint64_t dropped) {
    OspreyGraph *g = ctx->graph;
    OspreyKey ck = osprey_kind_region_key(kind, region);
    OspreyKindRegionCount *c = g_hash_table_lookup(g->kind_region, &ck);
    if (c == NULL) {
        c = g_new0(OspreyKindRegionCount, 1);
        g_hash_table_insert(g->kind_region, osprey_key_new(&ck), c);
    }
    c->kept += kept;
    c->dropped += dropped;
    if (dropped > 0 && g->limit_rows < 4096) {
        g->limit_rows++;
        log_msg("[osprey] [limit] [kind %u] [region %llx] [kept %llu] "
                "[dropped %llu]\n",
                (unsigned)kind,
                (unsigned long long)region->site_offset,
                (unsigned long long)c->kept, (unsigned long long)c->dropped);
    }
}

static bool kr_has_space(OspreyContext *ctx, uint8_t kind,
                         const OspreyRegionId *region) {
    OspreyGraph *g = ctx->graph;
    OspreyKey ck = osprey_kind_region_key(kind, region);
    OspreyKindRegionCount *c = g_hash_table_lookup(g->kind_region, &ck);
    if (c == NULL) return true;
    return c->kept < ctx->config.max_candidates_per_kind_region;
}

/* ------------------------------------------------------------------ */
/* Region extent (observed access bounds or allocation size)          */
/* ------------------------------------------------------------------ */

/* Low/high offsets observed for a region across all fact families. */
static bool region_extent(OspreyContext *ctx, const OspreyRegionId *region,
                          int64_t *lo, int64_t *hi) {
    bool any = false;
    int64_t l = 0, h = 0;
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *f = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        if (!same_region(&f->chunk.address.region, region)) continue;
        int64_t o = f->chunk.address.offset;
        int64_t e = o + (int64_t)f->chunk.size;
        if (!any || o < l) l = o;
        if (!any || e > h) h = e;
        any = true;
    }
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        OspreyBaseFact *b = &g_array_index(ctx->base_facts, OspreyBaseFact, i);
        if (!same_region(&b->chunk.address.region, region)) continue;
        int64_t o = b->chunk.address.offset;
        int64_t e = o + (int64_t)b->chunk.size;
        if (!any || o < l) l = o;
        if (!any || e > h) h = e;
        any = true;
    }
    if (region->kind == OSPREY_REGION_HEAP_SITE) {
        for (guint i = 0; i < ctx->alloc_facts->len; i++) {
            OspreyMallocFact *f = &g_array_index(ctx->alloc_facts,
                                                 OspreyMallocFact, i);
            if (f->site_pc != region->site_offset) continue;
            int64_t e = f->requested_size;
            if (!any) { l = 0; h = e; any = true; }
            else if (e > h) h = e;
        }
    }
    if (!any) return false;
    *lo = l;
    *hi = h;
    return true;
}

/* Aligned starts for a region: observed chunk start offsets. */
static void region_start_offsets(OspreyContext *ctx,
                                 const OspreyRegionId *region,
                                 GArray *offsets /* int64_t */) {
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *f = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        if (!same_region(&f->chunk.address.region, region)) continue;
        int64_t o = f->chunk.address.offset;
        bool seen = false;
        for (guint j = 0; j < offsets->len; j++) {
            if (g_array_index(offsets, int64_t, j) == o) { seen = true; break; }
        }
        if (!seen) g_array_append_val(offsets, o);
    }
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        OspreyBaseFact *b = &g_array_index(ctx->base_facts, OspreyBaseFact, i);
        if (!same_region(&b->chunk.address.region, region)) continue;
        int64_t o = b->chunk.address.offset;
        bool seen = false;
        for (guint j = 0; j < offsets->len; j++) {
            if (g_array_index(offsets, int64_t, j) == o) { seen = true; break; }
        }
        if (!seen) g_array_append_val(offsets, o);
    }
    insertion_sort_i64(offsets);
}

/* ------------------------------------------------------------------ */
/* R08/R09: alloc-unit facts per heap site                             */
/* ------------------------------------------------------------------ */

static bool alloc_unit_for_region(OspreyContext *ctx,
                                  const OspreyRegionId *region,
                                  int64_t *unit_out, bool *singleton_out) {
    /* sorted distinct successful requested sizes at this site */
    GArray *sizes = g_array_new(FALSE, FALSE, sizeof(int64_t));
    for (guint i = 0; i < ctx->alloc_facts->len; i++) {
        OspreyMallocFact *f = &g_array_index(ctx->alloc_facts,
                                             OspreyMallocFact, i);
        if (f->site_pc != region->site_offset) continue;
        int64_t s = (int64_t)f->requested_size;
        bool seen = false;
        for (guint j = 0; j < sizes->len; j++) {
            if (g_array_index(sizes, int64_t, j) == s) { seen = true; break; }
        }
        if (!seen) g_array_append_val(sizes, s);
    }
    if (sizes->len == 0) {
        g_array_free(sizes, TRUE);
        return false;
    }
    insertion_sort_i64(sizes);
    if (sizes->len == 1) {
        /* R08 ConstantAllocSize */
        *unit_out = g_array_index(sizes, int64_t, 0);
        if (singleton_out) *singleton_out = true;
    } else {
        /* R09 AllocUnit: gcd of successive size differences */
        int64_t g = 0;
        for (guint i = 1; i < sizes->len; i++) {
            int64_t d = g_array_index(sizes, int64_t, i) -
                        g_array_index(sizes, int64_t, i - 1);
            g = (g == 0) ? d : gcd_i64(g, d);
        }
        if (g == 0) {
            g_array_free(sizes, TRUE);
            return false;
        }
        *unit_out = g;
        if (singleton_out) *singleton_out = false;
    }
    g_array_free(sizes, TRUE);
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

/* CC01/CC02: constant alloc size / alloc unit per heap site. */
static void instantiate_cc01_cc02(OspreyContext *ctx) {
    GHashTable *sites = g_hash_table_new_full(g_direct_hash, g_direct_equal,
                                              NULL, NULL);
    for (guint i = 0; i < ctx->alloc_facts->len; i++) {
        OspreyMallocFact *f = &g_array_index(ctx->alloc_facts,
                                             OspreyMallocFact, i);
        if (g_hash_table_lookup(sites, GSIZE_TO_POINTER((gsize)f->site_pc)) !=
            NULL)
            continue;
        g_hash_table_insert(sites, GSIZE_TO_POINTER((gsize)f->site_pc),
                            GSIZE_TO_POINTER(1));
        OspreyRegionId h;
        h.kind = OSPREY_REGION_HEAP_SITE;
        h.code_image_id = 0;
        h.site_offset = f->site_pc;
        int64_t unit;
        bool singleton = false;
        if (!alloc_unit_for_region(ctx, &h, &unit, &singleton)) continue;
        if (unit < 0) continue;
        OspreyVarPayload pf;
        memset(&pf, 0, sizeof(pf));
        pf.heap_fold.region = h;
        pf.heap_fold.size = (uint64_t)unit;
        uint32_t vfold = osprey_intern_var_id(ctx, OSPREY_PRED_FOLDABLE_HEAP, &pf);
        if (vfold == UINT32_MAX) continue;
        uint32_t ids[1] = { vfold };
        /* CC02: FoldableHeap(i,s) prior (positive support); CC01's
         * UnfoldableHeap(i,s) ∧ FoldableHeap(i,0) is emitted when a
         * constant size exists (sizes->len == 1 handled by the same
         * helper; emit the CC01 pair then). */
        if (singleton) {
            /* CC01: ConstantAllocSize(i,s) : p↑ UnfoldableHeap(i,s) ∧
             * FoldableHeap(i,0); antecedent is a deterministic fact, so
             * each consequent is a unary positive factor. */
            OspreyVarPayload pu;
            memset(&pu, 0, sizeof(pu));
            pu.heap_fold.region = h;
            pu.heap_fold.size = (uint64_t)unit;
            uint32_t vunf = osprey_intern_var_id(ctx, OSPREY_PRED_UNFOLDABLE_HEAP, &pu);
            OspreyVarPayload pz;
            memset(&pz, 0, sizeof(pz));
            pz.heap_fold.region = h;
            pz.heap_fold.size = 0; /* FoldableHeap(i,0): no foldable tail */
            uint32_t vzero = osprey_intern_var_id(ctx, OSPREY_PRED_FOLDABLE_HEAP, &pz);
            if (vunf != UINT32_MAX) {
                uint32_t ids1[1] = { vunf };
                osprey_factor_add(ctx, OSPREY_RULE_CC01, UINT16_MAX, false, P_UP,
                           ids1, 1);
            }
            if (vzero != UINT32_MAX) {
                uint32_t ids1[1] = { vzero };
                osprey_factor_add(ctx, OSPREY_RULE_CC01, UINT16_MAX, false, P_UP,
                           ids1, 1);
            }
        }
        /* CC02: AllocUnit(i,s) -> FoldableHeap(i,s) unary prior */
        osprey_factor_add(ctx, OSPREY_RULE_CC02, UINT16_MAX, false, P_UP, ids, 1);
    }
    g_hash_table_destroy(sites);
}

/* CC03: PrimitiveVar(v) in heap H_i -> UnfoldableHeap(i, o+s). */
static void instantiate_cc03(OspreyContext *ctx) {
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *a = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        if (a->chunk.address.region.kind != OSPREY_REGION_HEAP_SITE)
            continue;
        OspreyVarPayload pv;
        memset(&pv, 0, sizeof(pv));
        pv.chunk = a->chunk;
        uint32_t v = osprey_intern_var_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pv);
        if (v == UINT32_MAX) continue;
        int64_t end;
        if (!osprey_check_add(a->chunk.address.offset,
                              (int64_t)a->chunk.size, &end))
            continue;
        OspreyVarPayload ph;
        memset(&ph, 0, sizeof(ph));
        ph.heap_fold.region = a->chunk.address.region;
        ph.heap_fold.size = (uint64_t)end;
        uint32_t u = osprey_intern_var_id(ctx, OSPREY_PRED_UNFOLDABLE_HEAP, &ph);
        if (u == UINT32_MAX) continue;
        uint32_t ids[2] = { v, u };
        osprey_factor_add(ctx, OSPREY_RULE_CC03, 1, false, P_UP, ids, 2);
    }
}

/* CD06: BaseAddr(i,v1,v2.a) ∧ Accessed(v1) ∧ Accessed(v2) ->
 * FieldOf(v1, v2.a). */
static void instantiate_cd06(OspreyContext *ctx) {
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        OspreyBaseFact *b = &g_array_index(ctx->base_facts, OspreyBaseFact, i);
        OspreyVarPayload pv;
        memset(&pv, 0, sizeof(pv));
        pv.chunk = b->chunk;
        uint32_t v = osprey_intern_var_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pv);
        if (v == UINT32_MAX) continue;
        OspreyVarPayload pf;
        memset(&pf, 0, sizeof(pf));
        pf.attached.chunk = b->chunk;
        pf.attached.base = b->base;
        uint32_t f = osprey_intern_var_id(ctx, OSPREY_PRED_FIELD_OF, &pf);
        if (f == UINT32_MAX) continue;
        uint32_t ids[2] = { v, f };
        /* CD06: BaseAddr(i,v1,v2.a) ∧ Accessed(v1) ∧ Accessed(v2)
         * -> FieldOf(v1,v2.a); antecedent facts are committed, so the
         * binary implication PrimitiveVar(v1) -> FieldOf(v1,v2.a) with
         * the §7.1 generic potential. */
        osprey_factor_add(ctx, OSPREY_RULE_CD06, 1, false, P_UP, ids, 2);
    }
}

/* CD11: PointsTo(v1, v2.a) ∧ Accessed(v1) ∧ Accessed(v2) ->
 * Pointer(v1, v2.a). */
static void instantiate_cd11(OspreyContext *ctx) {
    for (guint i = 0; i < ctx->points_facts->len; i++) {
        OspreyPointsToFact *p = &g_array_index(ctx->points_facts,
                                               OspreyPointsToFact, i);
        OspreyVarPayload pv;
        memset(&pv, 0, sizeof(pv));
        pv.chunk = p->pointer_chunk;
        uint32_t v1 = osprey_intern_var_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pv);
        if (v1 == UINT32_MAX) continue;
        OspreyVarPayload pp;
        memset(&pp, 0, sizeof(pp));
        pp.attached.chunk = p->pointer_chunk;
        pp.attached.base = p->target;
        uint32_t po = osprey_intern_var_id(ctx, OSPREY_PRED_POINTER, &pp);
        if (po == UINT32_MAX) continue;
        uint32_t ids[2] = { v1, po };
        /* CD11: PointsTo(v1,v2.a) ∧ Accessed(v1) ∧ Accessed(v2)
         * -> Pointer(v1,v2.a); facts already committed, so binary
         * PrimitiveVariable(v1) -> Pointer(v1,v2.a). */
        osprey_factor_add(ctx, OSPREY_RULE_CD11, 1, false, P_UP, ids, 2);
    }
}

/* CD10: FieldOf(v,a1) ↔ p↓ FieldOf(v,a2) for a1 != a2 (exclusion). */
static void instantiate_cd10(OspreyContext *ctx) {
    OspreyGraph *g = ctx->graph;
    for (guint i = 0; i < g->vars->len; i++) {
        OspreyVar *v1 = &g_array_index(g->vars, OspreyVar, i);
        if (v1->kind != OSPREY_PRED_FIELD_OF) continue;
        for (guint j = i + 1; j < g->vars->len; j++) {
            OspreyVar *v2 = &g_array_index(g->vars, OspreyVar, j);
            if (v2->kind != OSPREY_PRED_FIELD_OF) continue;
            if (!chunk_equal(&v1->payload.attached.chunk,
                             &v2->payload.attached.chunk))
                continue;
            if (address_equal(&v1->payload.attached.base,
                              &v2->payload.attached.base))
                continue;
            uint32_t ids[2] = { v1->id, v2->id };
            osprey_factor_add(ctx, OSPREY_RULE_CD10, 0, true, P_DN, ids, 2);
            osprey_factor_add(ctx, OSPREY_RULE_CD10, 1, true, P_DN, ids, 2);
        }
    }
}

/* CD01/CD02/CD03: hint -> HomoSegment(a1,a2,s). */
static void instantiate_cd01_03(OspreyContext *ctx) {
    OspreyGraph *g = ctx->graph;
    for (guint i = 0; i < g->hints->len; i++) {
        OspreyHint *h = &g_array_index(g->hints, OspreyHint, i);
        if (!kr_has_space(ctx, OSPREY_PRED_HOMO_SEGMENT, &h->a1.region)) {
            kr_account(ctx, OSPREY_PRED_HOMO_SEGMENT, &h->a1.region, 0, 1);
            continue;
        }
        /* §9.3: align starts to observed chunk starts */
        GArray *starts = g_array_new(FALSE, FALSE, sizeof(int64_t));
        region_start_offsets(ctx, &h->a1.region, starts);
        bool aligned = false;
        for (guint k = 0; k < starts->len; k++) {
            if (g_array_index(starts, int64_t, k) == h->a1.offset) {
                aligned = true;
                break;
            }
        }
        g_array_free(starts, TRUE);
        if (!aligned) {
            kr_account(ctx, OSPREY_PRED_HOMO_SEGMENT, &h->a1.region, 0, 1);
            continue;
        }
        OspreyVarPayload pv;
        memset(&pv, 0, sizeof(pv));
        pv.segment.a1 = h->a1;
        pv.segment.a2 = h->a2;
        pv.segment.size = h->size;
        uint32_t v = osprey_intern_var_id(ctx, OSPREY_PRED_HOMO_SEGMENT, &pv);
        if (v == UINT32_MAX) continue;
        double ps = P_UP;
        if (ctx->total_samples > 0) {
            double r = (double)h->instances / (double)ctx->total_samples;
            ps = P_UP * (r > 1.0 ? 1.0 : r);
            if (ps < P_DN) ps = P_DN;
        }
        uint16_t rule = (h->kind == 0) ? OSPREY_RULE_CD01 :
                        (h->kind == 1) ? OSPREY_RULE_CD03 :
                                         OSPREY_RULE_CD02;
        uint32_t ids[1] = { v };
        osprey_factor_add(ctx, rule, 0, false, ps, ids, 1);
        kr_account(ctx, OSPREY_PRED_HOMO_SEGMENT, &h->a1.region, 1, 0);
    }
}

/* CD04 closure: from (a1,a1',s1) and (a2,a2',s2) with 0 < a2-a1 < s1,
 * extend HomoSegment(a1,a1',(a2-a1)+s2); negative direction excludes.
 * Instances are bounded by the candidate cap. */
static void closure_cd04(OspreyContext *ctx) {
    OspreyGraph *g = ctx->graph;
    guint base_len = g->hints->len;
    for (guint i = 0; i < base_len; i++) {
        OspreyHint *h1 = &g_array_index(g->hints, OspreyHint, i);
        for (guint j = 0; j < base_len; j++) {
            if (i == j) continue;
            OspreyHint *h2 = &g_array_index(g->hints, OspreyHint, j);
            int64_t d;
            if (!offset_between(&h2->a1, &h1->a1, &d)) continue;
            if (!(d > 0 && d < h1->size)) continue;
            if (!same_region_addr(&h1->a1, &h2->a1)) continue;
            /* union length: (a2-a1) + s2 */
            int64_t len;
            if (!osprey_check_add(d, h2->size, &len)) continue;
            if (len <= 0) continue;
            if (!kr_has_space(ctx, OSPREY_PRED_HOMO_SEGMENT, &h1->a1.region)) {
                kr_account(ctx, OSPREY_PRED_HOMO_SEGMENT, &h1->a1.region, 0, 1);
                continue;
            }
            /* cap extended length to observed region extent (§9.3) */
            int64_t lo, hi;
            if (!region_extent(ctx, &h1->a1.region, &lo, &hi)) continue;
            if (h1->a1.offset < lo) continue;
            int64_t end;
            if (!osprey_check_add(h1->a1.offset, len, &end)) continue;
            if (end > hi) continue;
            /* a1 starts are observed chunk starts by construction
             * (hints only reference observed chunk addresses) */
            OspreyAddress a1p = h1->a2;
            OspreyVarPayload pv;
            memset(&pv, 0, sizeof(pv));
            pv.segment.a1 = h1->a1;
            pv.segment.a2 = a1p;
            pv.segment.size = len;
            uint32_t v = osprey_intern_var_id(ctx, OSPREY_PRED_HOMO_SEGMENT, &pv);
            if (v == UINT32_MAX) continue;
            uint32_t ids[1] = { v };
            osprey_factor_add(ctx, OSPREY_RULE_CD04, 0, false, P_UP, ids, 1);
            g->cd04_extensions++;
        }
    }
}

/* ------------------------------------------------------------------ */
/* Secondary deterministic rules (CB02-CB09, CC04/CC05, CD07, CD08)     */
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
        status = osprey_candidate_select(
            ctx, (const OspreyCandidateProposal *)proposals->data,
            proposals->len);
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

/* CC04/CC05: UnfoldableHeap pairwise (exclusion / monotonic support). */
static void cc04_cc05(OspreyContext *ctx)
{
    OspreyGraph *g = ctx->graph;
    for (guint i = 0; i < g->vars->len; i++) {
        OspreyVar *u1 = &g_array_index(g->vars, OspreyVar, i);
        if (u1->kind != OSPREY_PRED_UNFOLDABLE_HEAP) continue;
        for (guint j = i + 1; j < g->vars->len; j++) {
            OspreyVar *u2 = &g_array_index(g->vars, OspreyVar, j);
            if (u2->kind != OSPREY_PRED_UNFOLDABLE_HEAP) continue;
            if (!same_region(&u1->payload.heap_fold.region,
                             &u2->payload.heap_fold.region)) continue;
            uint64_t s1 = u1->payload.heap_fold.size;
            uint64_t s2 = u2->payload.heap_fold.size;
            if (s1 != s2) {
                /* CC04: exclusion */
                uint32_t ids[2] = { u1->id, u2->id };
                osprey_factor_add(ctx, OSPREY_RULE_CC04, 0, true, P_DN, ids, 2);
                osprey_factor_add(ctx, OSPREY_RULE_CC04, 1, true, P_DN, ids, 2);
            } else if (s1 < s2) {
                /* CC05: s1 <= s2 support */
                uint32_t ids[2] = { u1->id, u2->id };
                osprey_factor_add(ctx, OSPREY_RULE_CC05, 1, false, P_UP, ids, 2);
            }
        }
    }
}

/* CD07: PrimitiveVar(v) in heap H_i -> FieldOf(v, <H_i,0>). */
static void cd07_heap_fields(OspreyContext *ctx)
{
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *a = &g_array_index(ctx->access_facts,
                                             OspreyAccessFact, i);
        if (a->chunk.address.region.kind != OSPREY_REGION_HEAP_SITE)
            continue;
        OspreyVarPayload pv;
        memset(&pv, 0, sizeof(pv));
        pv.chunk = a->chunk;
        uint32_t v = osprey_intern_var_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pv);
        if (v == UINT32_MAX) continue;
        OspreyVarPayload pf;
        memset(&pf, 0, sizeof(pf));
        pf.attached.chunk = a->chunk;
        pf.attached.base.region = a->chunk.address.region;
        pf.attached.base.offset = 0;
        uint32_t f = osprey_intern_var_id(ctx, OSPREY_PRED_FIELD_OF, &pf);
        if (f == UINT32_MAX) continue;
        uint32_t ids[2] = { v, f };
        osprey_factor_add(ctx, OSPREY_RULE_CD07, 1, false, P_UP, ids, 2);
    }
}

/* CD08: FieldOf(v1,a1) ∧ HomoSegment(a1,a2,s) -> FieldOf(v2,a2) for
 * v1.a=a1+n, v2.a=a2+n, 1<=n<=s.  Creates v2 FieldOf candidates
 * (bounded per region). */
static void cd08_fields(OspreyContext *ctx)
{
    OspreyGraph *g = ctx->graph;
    GArray *homos = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    GArray *fields = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    for (guint i = 0; i < g->vars->len; i++) {
        OspreyVar *v = &g_array_index(g->vars, OspreyVar, i);
        if (v->kind == OSPREY_PRED_HOMO_SEGMENT) {
            uint32_t id = v->id;
            g_array_append_val(homos, id);
        } else if (v->kind == OSPREY_PRED_FIELD_OF) {
            uint32_t id = v->id;
            g_array_append_val(fields, id);
        }
    }
    for (guint hi = 0; hi < homos->len; hi++) {
        uint32_t hid = g_array_index(homos, uint32_t, hi);
        OspreyVar *h = &g_array_index(g->vars, OspreyVar, hid);
        const OspreyAddress *a1 = &h->payload.segment.a1;
        const OspreyAddress *a2 = &h->payload.segment.a2;
        int64_t s = h->payload.segment.size;
        if (s <= 0) continue;
        for (guint fi = 0; fi < fields->len; fi++) {
            uint32_t fid = g_array_index(fields, uint32_t, fi);
            OspreyVar *f1 = &g_array_index(g->vars, OspreyVar, fid);
            const OspreyChunk *c1 = &f1->payload.attached.chunk;
            int64_t n;
            if (!osprey_check_sub(c1->address.offset, a1->offset, &n))
                continue;
            if (!(n >= 1 && n <= s)) continue;
            if (!same_region(&c1->address.region, &a1->region)) continue;
            /* partner chunk at a2 + n, same size */
            if (!kr_has_space(ctx, OSPREY_PRED_FIELD_OF, &a2->region)) {
                kr_account(ctx, OSPREY_PRED_FIELD_OF, &a2->region, 0, 1);
                continue;
            }
            OspreyChunk c2 = *c1;
            c2.address.region = a2->region;
            int64_t off2;
            if (!osprey_check_add(a2->offset, n, &off2)) continue;
            c2.address.offset = off2;
            OspreyVarPayload pf;
            memset(&pf, 0, sizeof(pf));
            pf.attached.chunk = c2;
            pf.attached.base = *a2;
            uint32_t f2 = osprey_intern_var_id(ctx, OSPREY_PRED_FIELD_OF, &pf);
            if (f2 == UINT32_MAX) continue;
            kr_account(ctx, OSPREY_PRED_FIELD_OF, &a2->region, 1, 0);
            uint32_t ids[3] = { fid, hid, f2 };
            osprey_factor_add(ctx, OSPREY_RULE_CD08, 2, false, P_UP, ids, 3);
        }
    }
    g_array_free(homos, TRUE);
    g_array_free(fields, TRUE);
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

/* Stage-3 secondary entry.  CB03-CB05 are fact/candidate-driven and are
 * exhausted to a fixed point; CC07 remains a later belief-dependent rule. */
OspreyStatus osprey_stage3_secondary(OspreyContext *ctx)
{
    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    if (ctx->graph == NULL || ctx->relations == NULL) {
        return OSPREY_INCOMPLETE_FACTS;
    }
    osprey_graph_set_stage(ctx->graph, OSPREY_GRAPH_SECONDARY);

    GHashTable *processed = g_hash_table_new_full(
        osprey_key_hash, osprey_key_equal, osprey_key_free, NULL);
    OspreyStatus status = OSPREY_OK;
    for (;;) {
        bool changed = false;
        status = secondary_array_round(ctx, processed, &changed);
        if (status != OSPREY_OK || !changed) break;
    }
    g_hash_table_destroy(processed);
    if (status != OSPREY_OK) return status;

    status = compile_cb09(ctx);
    if (status != OSPREY_OK) return status;

    /* The remaining calls are the pre-existing Stage-3.4 families.  CA08
     * is deliberately repeated after their field candidates are present. */
    cc04_cc05(ctx);
    cd07_heap_fields(ctx);
    cd08_fields(ctx);
    status = compile_ca08(ctx);
    if (status != OSPREY_OK) return status;
    status = cb06_hard_false(ctx);
    if (status != OSPREY_OK) return status;

    if (ctx->last_status != OSPREY_OK) return ctx->last_status;
    OspreyGraph *graph = ctx->graph;
    log_msg("[osprey] [graph] [stage secondary] [vars %u] [factors %u]\n",
            graph->vars->len, graph->factors->len);
    return OSPREY_OK;
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

    /* R10-R12 hint extraction remains deterministic and parent-local. */
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

    /* Stage 3.4 families are retained in this coordinator until their own
     * review boundary.  Their fields become eligible for CA08 below. */
    instantiate_cc01_cc02(ctx);
    instantiate_cc03(ctx);
    instantiate_cd01_03(ctx);
    instantiate_cd06(ctx);
    instantiate_cd11(ctx);

    closure_cd04(ctx);
    instantiate_cd10(ctx);
    status = compile_ca08(ctx);
    if (status != OSPREY_OK) return status;

    uint32_t components = osprey_graph_component_count(graph);
    if (ctx->last_status != OSPREY_OK) return ctx->last_status;
    log_msg("[osprey] [graph] [stage base] [vars %u] [factors %u] "
            "[components %u] [hints %llu] [cd04 %llu]\n",
            graph->vars->len, graph->factors->len, components,
            (unsigned long long)graph->hint_instances,
            (unsigned long long)graph->cd04_extensions);
    return OSPREY_OK;
}
