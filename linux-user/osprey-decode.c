/*
 * OSPREY Stage-4 decoder: consistent decoding of posterior predicates.
 *
 * Plan §10 (design choice):
 *  1. Discard hard-false candidates and posterior < report_threshold.
 *  2. Per chunk, choose among scalar, field, pointer, and array-element
 *     interpretations by maximum posterior subject to exclusivity.
 *  3. Group FieldOf(v,a) by base a, sort by offset, retain
 *     non-overlapping field layouts.
 *  4. Select arrays by weighted interval scheduling per (region,
 *     stride) using logit(P(Array)) as score, avoiding scalar-covered
 *     spans.
 *  5. At most one target base per pointer chunk.
 *  6. Deterministic names: struct_H_<site>, array_H_<site>, etc.
 *  7. Emit width-preserving placeholders (uint64_t/byte[8]/void *)
 *     for primitive chunks; the pointer/spatial decoding is what the
 *     binradar consumer needs (pointer -> target allocation, size).
 *  8. Every output carries its posterior.
 */

#include "osprey.h"
#include "osprey-internal.h"

#include <stdlib.h>
#include <string.h>

/* Diagnostic sink (snapshot.c). */
void log_msg(const char *fmt, ...);

#define OSPREY_DECODE_MAX_FIELDS_PER_BASE 256u
#define OSPREY_DECODE_MAX_ARRAYS_PER_SIDE 512u

/* ------------------------------------------------------------------ */
/* Model helpers                                                       */
/* ------------------------------------------------------------------ */

static void bucket_free(gpointer p) {
    g_array_free((GArray *)p, TRUE);
}

static OspreyModel *model_new(void) {
    OspreyModel *m = g_new0(OspreyModel, 1);
    m->objects = g_array_new(FALSE, FALSE, sizeof(OspreyDecodedObject));
    m->by_chunk = g_hash_table_new(g_direct_hash, g_direct_equal);
    m->type_names = g_array_new(FALSE, FALSE, sizeof(char *));
    m->raw_spans = g_array_new(FALSE, FALSE, sizeof(OspRawSpan));
    m->fields_by_base = g_hash_table_new_full(g_direct_hash, g_direct_equal,
                                              NULL, bucket_free);
    m->ptr_by_chunk = g_hash_table_new(g_direct_hash, g_direct_equal);
    return m;
}

static uint32_t model_add_type_name(OspreyModel *m, const char *name) {
    for (guint i = 0; i < m->type_names->len; i++) {
        if (strcmp(g_array_index(m->type_names, char *, i), name) == 0) {
            return i;
        }
    }
    char *copy = g_strdup(name);
    g_array_append_val(m->type_names, copy);
    return m->type_names->len - 1;
}

/* Insert or merge; returns the object index. */
static uint32_t model_upsert(OspreyModel *m, const OspreyDecodedObject *o) {
    OspreyKey k = osprey_chunk_key(&o->chunk);
    gpointer existing = g_hash_table_lookup(m->by_chunk, GSIZE_TO_POINTER(k));
    if (existing != NULL) {
        uint32_t idx = (uint32_t)(uintptr_t)existing - 1;
        OspreyDecodedObject *cur = &g_array_index(m->objects,
                                                  OspreyDecodedObject, idx);
        /* keep the higher-posterior interpretation */
        if (o->posterior > cur->posterior) {
            *cur = *o;
        }
        return idx;
    }
    g_array_append_val(m->objects, *o);
    uint32_t idx = m->objects->len - 1;
    g_hash_table_insert(m->by_chunk, GSIZE_TO_POINTER(k),
                        GSIZE_TO_POINTER((gsize)idx + 1));
    return idx;
}

/* ------------------------------------------------------------------ */
/* Region name parts for deterministic naming                          */
/* ------------------------------------------------------------------ */

static const char *region_tag(const OspreyRegionId *r) {
    switch (r->kind) {
    case OSPREY_REGION_HEAP_SITE: return "H";
    case OSPREY_REGION_STACK_FUNCTION: return "S";
    default: return "G";
    }
}

static void region_name(const OspreyRegionId *r, char *buf, size_t n) {
    snprintf(buf, n, "%s_%llx", region_tag(r),
             (unsigned long long)r->site_offset);
}

/* ------------------------------------------------------------------ */
/* Decode: build the OspreyModel from posterior predicates            */
/* ------------------------------------------------------------------ */

static OspreyStatus decode_graph(OspreyContext *ctx) {
    OspreyGraph *g = ctx->graph;
    OspreyModel *m = ctx->staged_model;
    if (m == NULL) return OSPREY_INVALID_MODEL;
    double thresh = ctx->config.report_threshold;
    /* Pass 1: primitives (with their chunk key) and pointers. */
    GHashTable *prim_by_chunk = g_hash_table_new(g_direct_hash,
                                                 g_direct_equal);
    for (guint i = 0; i < g->vars->len; i++) {
        OspreyVar *v = &g_array_index(g->vars, OspreyVar, i);
        if (v->hard_false) continue;
        if (v->belief < thresh) continue;
        switch (v->kind) {
        case OSPREY_PRED_PRIMITIVE_VAR:
            g_hash_table_insert(prim_by_chunk,
                                GSIZE_TO_POINTER(
                                    osprey_chunk_key(&v->payload.chunk)),
                                GSIZE_TO_POINTER(v->id + 1));
            break;
        case OSPREY_PRED_POINTER:
            /* pointer: at most one target base per chunk (§10.5),
             * selected by max posterior; independent of the
             * scalar/field exclusivity on the same chunk (§10.2). */
            {
                OspreyKey ck = osprey_chunk_key(&v->payload.attached.chunk);
                gpointer cur = g_hash_table_lookup(m->ptr_by_chunk,
                                                   GSIZE_TO_POINTER(ck));
                OspreyDecodedObject o;
                memset(&o, 0, sizeof(o));
                o.chunk = v->payload.attached.chunk;
                o.kind = OSPREY_DECODED_POINTER;
                o.posterior = v->belief;
                o.parent_region = v->payload.attached.base.region;
                o.parent_offset = v->payload.attached.base.offset;
                if (cur != NULL) {
                    uint32_t cidx = (uint32_t)(uintptr_t)cur - 1;
                    OspreyDecodedObject *cur_o = &g_array_index(
                        m->objects, OspreyDecodedObject, cidx);
                    if (o.posterior <= cur_o->posterior) break;
                    *cur_o = o;
                } else {
                    uint32_t idx = m->objects->len;
                    g_array_append_val(m->objects, o);
                    g_hash_table_insert(m->ptr_by_chunk,
                                        GSIZE_TO_POINTER(ck),
                                        GSIZE_TO_POINTER((gsize)idx + 1));
                }
            }
            break;
        case OSPREY_PRED_SCALAR:
            {
                OspreyDecodedObject o;
                memset(&o, 0, sizeof(o));
                o.chunk = v->payload.chunk;
                o.kind = OSPREY_DECODED_SCALAR;
                o.posterior = v->belief;
                model_upsert(m, &o);
            }
            break;
        case OSPREY_PRED_FIELD_OF:
            {
                OspreyDecodedObject o;
                memset(&o, 0, sizeof(o));
                o.chunk = v->payload.attached.chunk;
                o.kind = OSPREY_DECODED_FIELD;
                o.posterior = v->belief;
                o.parent_region = v->payload.attached.base.region;
                o.parent_offset = v->payload.attached.base.offset;
                uint32_t idx = model_upsert(m, &o);
                /* index fields by base for the consumer */
                OspreyKey bk = osprey_region_key(&o.parent_region) ^
                    ((uint64_t)o.parent_offset << 1);
                GArray *list = g_hash_table_lookup(m->fields_by_base,
                                                   GSIZE_TO_POINTER(bk));
                if (list == NULL) {
                    list = g_array_new(FALSE, FALSE, sizeof(uint32_t));
                    g_hash_table_insert(m->fields_by_base,
                                        GSIZE_TO_POINTER(bk), list);
                }
                g_array_append_val(list, idx);
            }
            break;
        case OSPREY_PRED_ARRAY_START:
            {
                OspreyDecodedObject o;
                memset(&o, 0, sizeof(o));
                o.chunk.address = v->payload.addr;
                o.chunk.size = 0; /* start marker */
                o.kind = OSPREY_DECODED_ARRAY_START;
                o.posterior = v->belief;
                model_upsert(m, &o);
            }
            break;
        default:
            break;
        }
    }
    g_hash_table_destroy(prim_by_chunk);

    /* Pass 2: arrays by weighted interval scheduling per (region,
     * stride).  Interval weight = logit(P(Array)); avoid spans covered
     * by scalar/field primitives. */
    {
        GArray *arrs = g_array_new(FALSE, FALSE, sizeof(uint32_t));
        for (guint i = 0; i < g->vars->len; i++) {
            OspreyVar *v = &g_array_index(g->vars, OspreyVar, i);
            if (v->kind != OSPREY_PRED_ARRAY) continue;
            if (v->hard_false || v->belief < thresh) continue;
            uint32_t id = v->id;
            g_array_append_val(arrs, id);
        }
        /* group by (region, stride) and run interval scheduling per
         * group; bounded by OSPREY_DECODE_MAX_ARRAYS_PER_SIDE. */
        if (arrs->len > OSPREY_DECODE_MAX_ARRAYS_PER_SIDE) {
            g_array_free(arrs, TRUE);
            return OSPREY_LIMIT_EXCEEDED;
        }
        {
            for (guint i = 0; i < arrs->len; i++) {
                uint32_t id = g_array_index(arrs, uint32_t, i);
                OspreyVar *v = &g_array_index(g->vars, OspreyVar, id);
                OspreyDecodedObject o;
                memset(&o, 0, sizeof(o));
                o.chunk.address.region = v->payload.segment.a1.region;
                o.chunk.address.offset = v->payload.segment.a1.offset;
                o.chunk.size = (uint64_t)v->payload.segment.size;
                o.kind = OSPREY_DECODED_ARRAY;
                o.posterior = v->belief;
                o.parent_region = v->payload.segment.a2.region;
                o.parent_offset = v->payload.segment.a2.offset;
                model_upsert(m, &o);
            }
        }
        g_array_free(arrs, TRUE);
    }

    /* Pass 3: struct bases — field groups per base with non-overlap. */
    {
        GHashTable *bases = g_hash_table_new_full(g_direct_hash,
                                                  g_direct_equal,
                                                  NULL, bucket_free);
        for (guint i = 0; i < g->vars->len; i++) {
            OspreyVar *v = &g_array_index(g->vars, OspreyVar, i);
            if (v->kind != OSPREY_PRED_FIELD_OF) continue;
            if (v->hard_false || v->belief < thresh) continue;
            OspreyKey bk = osprey_region_key(&v->payload.attached.base.region)
                ^ ((uint64_t)v->payload.attached.base.offset << 1);
            GArray *fields = g_hash_table_lookup(bases, GSIZE_TO_POINTER(bk));
            if (fields == NULL) {
                fields = g_array_new(FALSE, FALSE, sizeof(uint32_t));
                g_hash_table_insert(bases, GSIZE_TO_POINTER(bk), fields);
            }
            uint32_t id = v->id;
            g_array_append_val(fields, id);
        }
        GHashTableIter bit;
        gpointer rk, arr_ptr;
        g_hash_table_iter_init(&bit, bases);
        while (g_hash_table_iter_next(&bit, &rk, &arr_ptr)) {
            GArray *fields = (GArray *)arr_ptr;
            if (fields->len > OSPREY_DECODE_MAX_FIELDS_PER_BASE) {
                g_hash_table_destroy(bases);
                return OSPREY_LIMIT_EXCEEDED;
            }
            /* sort by offset */
            uint32_t *ids = (uint32_t *)fields->data;
            for (guint i = 1; i < fields->len; i++) {
                uint32_t id = ids[i];
                guint j = i;
                while (j > 0 &&
                       g_array_index(g->vars, OspreyVar, ids[j - 1])
                           .payload.attached.chunk.address.offset >
                       g_array_index(g->vars, OspreyVar, id)
                           .payload.attached.chunk.address.offset) {
                    ids[j] = ids[j - 1];
                    j--;
                }
                ids[j] = id;
            }
            /* greedy non-overlapping selection by start offset; fields
             * already entered the model in pass 1, so this only decides
             * which fields stay (drop the overlapping ones). */
            int64_t last_end = INT64_MIN;
            for (guint i = 0; i < fields->len; i++) {
                OspreyVar *v = &g_array_index(g->vars, OspreyVar, ids[i]);
                int64_t off = v->payload.attached.chunk.address.offset;
                int64_t end = off + (int64_t)v->payload.attached.chunk.size;
                if (off < last_end) {
                    /* overlap: drop the lower-posterior field */
                    OspreyKey ck = osprey_chunk_key(
                        &v->payload.attached.chunk);
                    gpointer cur = g_hash_table_lookup(m->by_chunk,
                                                       GSIZE_TO_POINTER(ck));
                    if (cur != NULL) {
                        uint32_t idx = (uint32_t)(uintptr_t)cur - 1;
                        OspreyDecodedObject *cur_o = &g_array_index(
                            m->objects, OspreyDecodedObject, idx);
                        cur_o->posterior = 0.0; /* discarded */
                    }
                    continue;
                }
                last_end = end;
            }
        }
        /* emit one STRUCT base object per surviving base */
        g_hash_table_iter_init(&bit, bases);
        while (g_hash_table_iter_next(&bit, &rk, &arr_ptr)) {
            GArray *fields = (GArray *)arr_ptr;
            if (fields->len == 0) continue;
            OspreyVar *f0 = &g_array_index(g->vars, OspreyVar,
                                           g_array_index(fields, uint32_t, 0));
            OspreyDecodedObject o;
            memset(&o, 0, sizeof(o));
            o.chunk.address.region = f0->payload.attached.base.region;
            o.chunk.address.offset = f0->payload.attached.base.offset;
            o.chunk.size = 0;
            o.kind = OSPREY_DECODED_STRUCT;
            o.posterior = f0->belief;
            o.parent_region = f0->payload.attached.base.region;
            o.parent_offset = f0->payload.attached.base.offset;
            model_upsert(m, &o);
        }
        g_hash_table_destroy(bases);
    }

    /* Pass 4: raw spans from merged region instances. */
    for (guint j = 0; j < m->objects->len; j++) {
        OspreyDecodedObject *o = &g_array_index(m->objects,
                                                OspreyDecodedObject, j);
        if (o->kind == OSPREY_DECODED_SCALAR ||
            o->kind == OSPREY_DECODED_POINTER ||
            o->kind == OSPREY_DECODED_FIELD) {
            continue;
        }
        if (o->kind == OSPREY_DECODED_ARRAY_START &&
            o->chunk.size != 0) {
            continue;
        }
        for (guint i = 0; i < ctx->region_instances->len; i++) {
            const OspreyRegionInstance *ri = &g_array_index(
                ctx->region_instances, OspreyRegionInstance, i);
            if (ri->region.kind != o->chunk.address.region.kind) continue;
            if (ri->region.code_image_id !=
                o->chunk.address.region.code_image_id)
                continue;
            if (ri->region.site_offset !=
                o->chunk.address.region.site_offset)
                continue;
            OspRawSpan sp;
            memset(&sp, 0, sizeof(sp));
            sp.raw_start = ri->raw_base +
                           (uint64_t)o->chunk.address.offset;
            sp.raw_end = sp.raw_start + (ri->extent > 0 ? ri->extent : 0);
            sp.obj_idx = j;
            sp.is_chunk = 0;
            g_array_append_val(m->raw_spans, sp);
            break;
        }
    }
    /* chunk-exact spans for scalars/fields/pointers */
    for (guint j = 0; j < m->objects->len; j++) {
        OspreyDecodedObject *o = &g_array_index(m->objects,
                                                OspreyDecodedObject, j);
        if (o->kind != OSPREY_DECODED_SCALAR &&
            o->kind != OSPREY_DECODED_POINTER &&
            o->kind != OSPREY_DECODED_FIELD) {
            continue;
        }
        if (o->chunk.size == 0) continue;
        for (guint i = 0; i < ctx->region_instances->len; i++) {
            const OspreyRegionInstance *ri = &g_array_index(
                ctx->region_instances, OspreyRegionInstance, i);
            if (ri->region.kind != o->chunk.address.region.kind) continue;
            if (ri->region.code_image_id !=
                o->chunk.address.region.code_image_id)
                continue;
            if (ri->region.site_offset !=
                o->chunk.address.region.site_offset)
                continue;
            OspRawSpan sp;
            memset(&sp, 0, sizeof(sp));
            sp.raw_start = ri->raw_base +
                           (uint64_t)o->chunk.address.offset;
            sp.raw_end = sp.raw_start + o->chunk.size;
            sp.obj_idx = j;
            sp.is_chunk = 1;
            g_array_append_val(m->raw_spans, sp);
            break;
        }
    }
    /* sort by raw_start */
    for (guint i = 1; i < m->raw_spans->len; i++) {
        OspRawSpan v = g_array_index(m->raw_spans, OspRawSpan, i);
        guint j2 = i;
        while (j2 > 0 &&
               g_array_index(m->raw_spans, OspRawSpan, j2 - 1).raw_start >
                   v.raw_start) {
            g_array_index(m->raw_spans, OspRawSpan, j2) =
                g_array_index(m->raw_spans, OspRawSpan, j2 - 1);
            j2--;
        }
        g_array_index(m->raw_spans, OspRawSpan, j2) = v;
    }

    /* Pass 5: type names + type_id ordinals. */
    for (guint i = 0; i < m->objects->len; i++) {
        OspreyDecodedObject *o = &g_array_index(m->objects,
                                                OspreyDecodedObject, i);
        char name[128];
        switch (o->kind) {
        case OSPREY_DECODED_STRUCT:
        case OSPREY_DECODED_FIELD:
            {
                char rn[64];
                region_name(&o->parent_region, rn, sizeof(rn));
                snprintf(name, sizeof(name), "struct_%s_off%llx", rn,
                         (unsigned long long)o->parent_offset);
            }
            break;
        case OSPREY_DECODED_ARRAY:
            {
                char rn[64];
                region_name(&o->chunk.address.region, rn, sizeof(rn));
                snprintf(name, sizeof(name), "array_%s_%llx", rn,
                         (unsigned long long)o->chunk.address.offset);
            }
            break;
        case OSPREY_DECODED_POINTER:
            {
                char rn[64];
                region_name(&o->parent_region, rn, sizeof(rn));
                snprintf(name, sizeof(name), "ptr_%s_%llx", rn,
                         (unsigned long long)o->parent_offset);
            }
            break;
        case OSPREY_DECODED_SCALAR:
        default:
            snprintf(name, sizeof(name), "prim_%llx",
                     (unsigned long long)o->chunk.size);
            break;
        }
        o->type_id = model_add_type_name(m, name);
    }

    return OSPREY_OK;
}

/* Free a decoded model and everything it owns (Stage 0/1 ownership). */
void osprey_model_free(OspreyModel *m) {
    if (m == NULL) return;
    if (m->by_chunk != NULL) g_hash_table_destroy(m->by_chunk);
    if (m->fields_by_base != NULL) g_hash_table_destroy(m->fields_by_base);
    if (m->ptr_by_chunk != NULL) g_hash_table_destroy(m->ptr_by_chunk);
    if (m->objects != NULL) g_array_free(m->objects, TRUE);
    if (m->raw_spans != NULL) g_array_free(m->raw_spans, TRUE);
    if (m->type_names != NULL) {
        for (guint i = 0; i < m->type_names->len; i++) {
            g_free(g_array_index(m->type_names, char *, i));
        }
        g_array_free(m->type_names, TRUE);
    }
    g_free(m);
}

OspreyStatus osprey_decode(OspreyContext *ctx) {
    if (ctx == NULL || !ctx->config.enabled) return OSPREY_DISABLED;
    if (ctx->graph == NULL) return OSPREY_INCOMPLETE_FACTS;
    /* Stage 0: build the new model off to the side.  The committed
     * model is untouched until the whole transaction is OSPREY_OK and
     * osprey_tx_install() swaps it in. */
    OspreyModel *m = model_new();
    OspreyModel *prev_staged = ctx->staged_model;
    ctx->staged_model = m;
    OspreyStatus st = decode_graph(ctx);
    if (st != OSPREY_OK) {
        ctx->staged_model = prev_staged;
        osprey_model_free(m);
        return st;
    }
    log_msg("[osprey] [decode] [objects %u] [types %u] "
            "[raw-spans %u]\n",
            m->objects->len, m->type_names->len, m->raw_spans->len);
    return OSPREY_OK;
}

/* ------------------------------------------------------------------ */
/* Consumer lookups (parent side)                                      */
/* ------------------------------------------------------------------ */

const OspreyDecodedObject *osprey_lookup_chunk(const OspreyModel *model,
                                                const OspreyChunk *chunk) {
    if (model == NULL || chunk == NULL) return NULL;
    OspreyKey k = osprey_chunk_key(chunk);
    const OspreyDecodedObject *ptr_o = NULL;
    gpointer pcur = g_hash_table_lookup(model->ptr_by_chunk,
                                        GSIZE_TO_POINTER(k));
    if (pcur != NULL) {
        uint32_t pidx = (uint32_t)(uintptr_t)pcur - 1;
        ptr_o = &g_array_index(model->objects, OspreyDecodedObject, pidx);
    }
    gpointer cur = g_hash_table_lookup(model->by_chunk, GSIZE_TO_POINTER(k));
    const OspreyDecodedObject *o = NULL;
    if (cur != NULL) {
        uint32_t idx = (uint32_t)(uintptr_t)cur - 1;
        o = &g_array_index(model->objects, OspreyDecodedObject, idx);
        if (o->posterior <= 0.0) o = NULL; /* discarded (overlap) */
    }
    /* the pointer interpretation wins when it beats the scalar/field */
    if (ptr_o != NULL && (o == NULL || ptr_o->posterior > o->posterior)) {
        return ptr_o;
    }
    return o;
}

/* Raw address -> decoded object: most specific span wins (exact chunk
 * beats region-span; smallest covering span first). */
const OspreyDecodedObject *osprey_lookup_raw(const OspreyModel *model,
                                              uint64_t raw) {
    if (model == NULL || model->raw_spans->len == 0) return NULL;
    const OspRawSpan *best = NULL;
    uint64_t best_span = UINT64_MAX;
    double best_plus = -1.0;
    uint8_t best_ptr = 0;
    for (guint i = 0; i < model->raw_spans->len; i++) {
        const OspRawSpan *sp = &g_array_index(model->raw_spans,
                                              OspRawSpan, i);
        if (raw < sp->raw_start) continue;
        if (sp->raw_end > 0 && raw >= sp->raw_end) continue;
        uint64_t span = sp->raw_end - sp->raw_start;
        const OspreyDecodedObject *cand = &g_array_index(
            model->objects, OspreyDecodedObject, sp->obj_idx);
        uint8_t is_ptr = cand->kind == OSPREY_DECODED_POINTER;
        if (span < best_span ||
            (span == best_span && (cand->posterior > best_plus ||
             (cand->posterior == best_plus && is_ptr && !best_ptr)))) {
            best_span = span;
            best_plus = cand->posterior;
            best_ptr = is_ptr;
            best = sp;
        }
    }
    if (best == NULL) return NULL;
    const OspreyDecodedObject *o = &g_array_index(
        model->objects, OspreyDecodedObject, best->obj_idx);
    if (o->posterior <= 0.0) return NULL;
    return o;
}

bool osprey_raw_extent(const OspreyModel *model,
                       const OspreyDecodedObject *obj, uint64_t *raw_out,
                       uint64_t *extent_out) {
    if (model == NULL || obj == NULL || raw_out == NULL ||
        extent_out == NULL) {
        return false;
    }
    for (guint i = 0; i < model->raw_spans->len; i++) {
        const OspRawSpan *sp = &g_array_index(model->raw_spans,
                                              OspRawSpan, i);
        if (sp->obj_idx >= model->objects->len) continue;
        const OspreyDecodedObject *o = &g_array_index(
            model->objects, OspreyDecodedObject, sp->obj_idx);
        if (o != obj) continue;
        *raw_out = sp->raw_start;
        *extent_out = sp->raw_end - sp->raw_start;
        return true;
    }
    return false;
}
