/*
 * OSPREY Stage-0 fail-closed transaction unit tests.
 *
 * Links the five OSPREY translation units (osprey.o, osprey-facts.o,
 * osprey-rules.o, osprey-infer.o, osprey-decode.o) from the tracer
 * build against a small stub environment (log_msg, is_valid_address,
 * guest_base, qemu mutex primitives) and drives the public API:
 *
 *  - merge validation rejects overflow / bad arithmetic / bad provenance
 *    identity / unsupported execution / version or capacity mismatch / malformed population /
 *    used>cap before appending any committed fact;
 *  - a rejected merge leaves the transaction non-OK, emits exactly one
 *    [osprey] [reject] row, and exposes no model;
 *  - osprey_analyze() stages the graph/model and installs them only on
 *    OSPREY_OK; variable/factor/decoder/exact-component caps and
 *    empty-graph incomplete facts reject the transaction;
 *  - a later rejected transaction hides the previously committed model
 *    from consumers (osprey_model() == NULL) while retaining it
 *    internally until the next successful transaction;
 *  - a fresh baseline transaction recovers from a previous rejection.
 *
 * Build: see tests/osprey/Makefile (target `unit`).
 */

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ucontext.h>
#include <unistd.h>

#include "osprey.h"
#include "osprey-internal.h"
#include "qemu/thread.h"
#include "provenance.h"
#include "sem-events.h"
#include "tcg/symbolic/symbolic-struct.h"

extern void helper_sem_mem_unsupported(CPUArchState *env, target_ulong pc,
                                       uint32_t reason);

/* ------------------------------------------------------------------ */
/* Stub environment                                                    */
/* ------------------------------------------------------------------ */

unsigned long guest_base = 0;

/* Provenance module externs (provenance.o links against these). */
int binradar_memcheck_enabled = 0;
uint64_t symbolic_start_code = 0;
uint64_t symbolic_end_code = 0;
Expr *pool = NULL;
Expr *next_free_expr = NULL;
Query *query_queue = NULL;
Query *next_query = NULL;

SnapshotMemRegion *mr_manager_heap_search_pub(target_ulong addr)
{
    (void)addr;
    return NULL;
}

static char g_test_log[1 << 20];
static size_t g_test_log_len = 0;
static int g_reject_rows = 0;

void log_msg(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    int n = vsnprintf(g_test_log + g_test_log_len,
                      sizeof(g_test_log) - g_test_log_len, fmt, ap);
    va_end(ap);
    if (n > 0) {
        if (strstr(g_test_log + g_test_log_len, "[reject]") != NULL) {
            g_reject_rows++;
        }
        g_test_log_len += (size_t)n;
        if (g_test_log_len > sizeof(g_test_log) - 1) {
            g_test_log_len = sizeof(g_test_log) - 1;
        }
    }
}

bool is_valid_address(target_ulong addr, bool for_snapshot)
{
    (void)addr;
    (void)for_snapshot;
    return false;
}

void qemu_mutex_init(QemuMutex *m)
{
    pthread_mutex_init(&m->lock, NULL);
}

void qemu_mutex_destroy(QemuMutex *m)
{
    pthread_mutex_destroy(&m->lock);
}

void qemu_mutex_lock_impl(QemuMutex *m, const char *file, const int line)
{
    (void)file;
    (void)line;
    pthread_mutex_lock(&m->lock);
}

void qemu_mutex_unlock_impl(QemuMutex *m, const char *file, const int line)
{
    (void)file;
    (void)line;
    pthread_mutex_unlock(&m->lock);
}

QemuMutexLockFunc qemu_mutex_lock_func = qemu_mutex_lock_impl;
QemuMutexTrylockFunc qemu_mutex_trylock_func = NULL;

static void test_sem_manifest_integrity(void);
static void test_sem_overwrite_fail_closed(void);
static void test_sem_access_class_and_flags(void);
static void test_address_origin_channels_and_producers(void);
static void test_address_shadow_reload(void);
static void test_f02_ea_selection(void);
static void test_base_fact_producer_merge(void);
static void test_value_origin_creation_and_transfer(void);
static void test_ordinary_f03_f04_publication(void);
static void test_osprey_shadow_overlap_invalidation(void);
static void test_modeled_copy_origins_and_facts(void);
static void test_copy_points_merge_and_dump(void);

void helper_sem_on_load(CPUArchState *env, uint32_t dst_idx,
                        target_ulong addr, target_ulong size,
                        target_ulong pc, uint32_t cls);
void helper_sem_on_store(CPUArchState *env, uint32_t src_idx,
                         target_ulong addr, target_ulong size,
                         target_ulong src_val, uint32_t cls);
void helper_sem_reg_lea(CPUArchState *env, uint32_t dst_idx,
                        uint32_t base_idx, target_ulong disp,
                        target_ulong dst_val, target_ulong base_val);
void helper_sem_set_pc(CPUArchState *env, target_ulong pc);

/* ------------------------------------------------------------------ */
/* Harness                                                             */
/* ------------------------------------------------------------------ */

static int failures = 0;

#define CHECK(cond, msg) do {                                            \
    if (!(cond)) {                                                       \
        fprintf(stderr, "FAIL: %s (line %d)\n", (msg), __LINE__);        \
        failures++;                                                      \
    }                                                                    \
} while (0)

static void reset_log(void)
{
    g_test_log_len = 0;
    g_reject_rows = 0;
    g_test_log[0] = '\0';
}

static OspreyConfig test_config(void)
{
    OspreyConfig c;
    memset(&c, 0, sizeof(c));
    c.enabled = true;
    c.shared_bytes = 1u << 20;
    c.max_facts = 262144;
    c.max_chunks_per_region = 8192;
    c.max_candidates_per_kind_region = 4096;
    c.max_variables = 100000;
    c.max_factors = 500000;
    c.max_exact_clique_vars = 20;
    c.report_threshold = 0.2;
    return c;
}

static OspreySharedRun *new_run(const OspreyConfig *c)
{
    size_t sz = osprey_shared_run_size(c);
    OspreySharedRun *run = g_malloc0(sz);
    osprey_shared_run_reset(run, 1, c);
    return run;
}

/* Two distinct 8-byte access facts: global region, offsets 0 and 8,
 * different PCs. */
static void fill_two_access_facts(OspreySharedRun *run)
{
    OspreyAccessFact f1, f2;
    memset(&f1, 0, sizeof(f1));
    f1.pc = 0x100;
    f1.chunk.address.region.kind = OSPREY_REGION_GLOBAL;
    f1.chunk.address.region.code_image_id = 0;
    f1.chunk.address.region.site_offset = 0;
    f1.chunk.address.offset = 0;
    f1.chunk.size = 8;
    f1.dynamic_count = 1;
    f1.sample_support = 1;
    f1.is_store = 0;
    f2 = f1;
    f2.pc = 0x200;
    f2.chunk.address.offset = 8;
    CHECK(osprey_table_insert_access(run, &f1) == 1, "insert f1");
    CHECK(osprey_table_insert_access(run, &f2) == 1, "insert f2");
}

/* ------------------------------------------------------------------ */
/* Merge validation                                                    */
/* ------------------------------------------------------------------ */

static void test_overflow_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->overflow = 1;

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "overflow merge status");
    CHECK(osprey_tx_status(ctx) == OSPREY_INCOMPLETE_FACTS,
          "overflow tx status");
    CHECK(strcmp(osprey_tx_stage(ctx), "merge") == 0, "overflow tx stage");
    CHECK(osprey_model(ctx) == NULL, "overflow no model");
    CHECK(ctx->access_facts->len == 0, "overflow no partial merge");
    CHECK(ctx->total_samples == 0, "overflow no sample count");
    CHECK(g_reject_rows == 1, "overflow exactly one reject row");
    CHECK(osprey_analyze(ctx) == OSPREY_INCOMPLETE_FACTS,
          "analyze preserves rejected merge");
    CHECK(g_reject_rows == 1, "analyze does not duplicate rejection");

    osprey_free(ctx);
    g_free(run);
}

static void test_bad_arithmetic_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->bad_arithmetic = 1;

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "bad-arith merge status");
    CHECK(osprey_tx_status(ctx) == OSPREY_INCOMPLETE_FACTS,
          "bad-arith tx status");
    CHECK(strcmp(osprey_tx_stage(ctx), "merge") == 0, "bad-arith tx stage");
    CHECK(ctx->access_facts->len == 0, "bad-arith no partial merge");
    CHECK(g_reject_rows == 1, "bad-arith exactly one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_bad_identity_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->bad_identity = 1;

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "bad-identity merge status");
    CHECK(osprey_tx_status(ctx) == OSPREY_INCOMPLETE_FACTS,
          "bad-identity tx status");
    CHECK(strcmp(osprey_tx_stage(ctx), "merge") == 0,
          "bad-identity tx stage");
    CHECK(ctx->access_facts->len == 0, "bad-identity no partial merge");
    CHECK(g_reject_rows == 1, "bad-identity exactly one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_version_mismatch_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->version = 9;

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "version merge status");
    CHECK(strcmp(osprey_tx_stage(ctx), "merge") == 0, "version tx stage");
    CHECK(ctx->access_facts->len == 0, "version no partial merge");
    CHECK(g_reject_rows == 1, "version exactly one reject row");

    osprey_free(ctx);
    g_free(run);

    /* A malformed prefix freeze must remain fail-closed after prepare;
     * the full-reset fallback cannot erase the pre-sample failure. */
    reset_log();
    ctx = osprey_new(&c);
    run = new_run(&c);
    run->version = 9;
    CHECK(!osprey_shared_run_freeze_prefix(ctx, run),
          "malformed prefix freeze fails");
    osprey_shared_run_prepare(ctx, run, 2);
    CHECK(run->version == OSPREY_SHARED_VERSION,
          "prepare restores canonical layout");
    CHECK(run->bad_arithmetic == 1,
          "prepare preserves prefix-freeze fatal state");
    st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS,
          "malformed prefix remains rejected");
    CHECK(g_reject_rows == 1, "malformed prefix one reject row");
    osprey_free(ctx);
    g_free(run);
    osprey_clear_pre_sample_fatal();
}

static void test_capacity_mismatch_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    CHECK(osprey_shared_run_size(&c) <=
              c.shared_bytes + sizeof(OspreySharedRun) + 256,
          "shared layout respects configured byte budget");
    run->access_cap = 0;

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "capacity merge status");
    CHECK(strcmp(osprey_tx_stage(ctx), "merge") == 0, "capacity tx stage");
    CHECK(ctx->access_facts->len == 0, "capacity no partial merge");
    CHECK(g_reject_rows == 1, "capacity exactly one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_population_mismatch_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->access_used = 1; /* header claims a record; storage is empty */

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "population merge status");
    CHECK(ctx->access_facts->len == 0, "population no partial merge");
    CHECK(ctx->total_samples == 0, "population no sample count");
    CHECK(g_reject_rows == 1, "population exactly one reject row");

    osprey_free(ctx);
    g_free(run);

    /* Boolean support is part of the shared format. */
    reset_log();
    ctx = osprey_new(&c);
    run = new_run(&c);
    OspreyAccessFact bad_support;
    memset(&bad_support, 0, sizeof(bad_support));
    bad_support.pc = 0x100;
    bad_support.chunk.address.region.kind = OSPREY_REGION_GLOBAL;
    bad_support.chunk.size = 8;
    bad_support.dynamic_count = 1;
    bad_support.sample_support = 2;
    CHECK(osprey_table_insert_access(run, &bad_support) == 1,
          "malformed support inserted for validation");
    st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS,
          "non-Boolean support rejected");
    CHECK(ctx->access_facts->len == 0,
          "non-Boolean support no partial merge");
    CHECK(g_reject_rows == 1, "non-Boolean support one reject row");
    osprey_free(ctx);
    g_free(run);

    /* The maintained unique-fact count must match prefix∪suffix. */
    reset_log();
    ctx = osprey_new(&c);
    run = new_run(&c);
    bad_support.sample_support = 1;
    CHECK(osprey_table_insert_access(run, &bad_support) == 1,
          "fact-count validation insert");
    run->total_facts_count = 0;
    st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS,
          "stale unique-fact count rejected");
    CHECK(ctx->access_facts->len == 0,
          "stale unique-fact count no partial merge");
    CHECK(g_reject_rows == 1, "stale fact count one reject row");
    osprey_free(ctx);
    g_free(run);
}

static void test_unsupported_execution_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->unsupported_execution = 1;

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_UNSUPPORTED_EXECUTION, "unsupported merge status");
    CHECK(osprey_tx_status(ctx) == OSPREY_UNSUPPORTED_EXECUTION,
          "unsupported tx status");
    CHECK(ctx->access_facts->len == 0, "unsupported no partial merge");
    CHECK(g_reject_rows == 1, "unsupported exactly one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_used_exceeds_cap_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    run->access_used = run->access_cap + 1;

    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "used>cap merge status");
    CHECK(strcmp(osprey_tx_stage(ctx), "merge") == 0, "used>cap tx stage");
    CHECK(ctx->access_facts->len == 0, "used>cap no partial merge");
    CHECK(g_reject_rows == 1, "used>cap exactly one reject row");

    osprey_free(ctx);
    g_free(run);
}

/* ------------------------------------------------------------------ */
/* Happy path + staged install + fail-closed consumer                  */
/* ------------------------------------------------------------------ */

static void test_happy_merge_analyze_and_hide(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    fill_two_access_facts(run);

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "happy merge");
    CHECK(ctx->access_facts->len == 2, "two facts merged");
    CHECK(ctx->total_samples == 1, "one sample committed");
    CHECK(osprey_tx_ok(ctx), "tx ok after merge");
    CHECK(osprey_model(ctx) == NULL, "old model hidden before install");
    CHECK(g_reject_rows == 0, "no reject row on happy merge");

    OspreyStatus st = osprey_analyze(ctx);
    CHECK(st == OSPREY_OK, "analyze ok");
    CHECK(osprey_tx_ok(ctx), "tx ok after analyze");
    CHECK(osprey_model(ctx) != NULL, "model installed on success");
    CHECK(ctx->graph != NULL, "graph committed on success");

    OspreySharedRun *run_pending = new_run(&c);
    fill_two_access_facts(run_pending);
    CHECK(osprey_parent_merge_sample(ctx, run_pending) == OSPREY_OK,
          "new merge starts transaction");
    CHECK(osprey_model(ctx) == NULL,
          "previous model hidden while new transaction is uncommitted");

    /* A later rejected transaction must hide the committed model from
     * consumers while retaining it internally. */
    OspreySharedRun *run2 = new_run(&c);
    run2->overflow = 1;
    CHECK(osprey_parent_merge_sample(ctx, run2) == OSPREY_INCOMPLETE_FACTS,
          "second merge rejects");
    CHECK(osprey_model(ctx) == NULL, "model hidden after rejection");
    CHECK(ctx->model != NULL, "committed model retained internally");
    CHECK(g_reject_rows == 1, "second transaction one reject row");

    osprey_free(ctx);
    g_free(run);
    g_free(run_pending);
    g_free(run2);
}

static void test_recovery_after_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *bad = new_run(&c);
    bad->bad_arithmetic = 1;
    CHECK(osprey_parent_merge_sample(ctx, bad) == OSPREY_INCOMPLETE_FACTS,
          "first merge rejects");
    CHECK(!osprey_tx_ok(ctx), "tx non-ok after rejection");

    /* A fresh baseline transaction recovers. */
    OspreySharedRun *good = new_run(&c);
    fill_two_access_facts(good);
    CHECK(osprey_parent_merge_sample(ctx, good) == OSPREY_OK,
          "recovery merge ok");
    CHECK(osprey_tx_ok(ctx), "tx ok after recovery merge");
    CHECK(osprey_analyze(ctx) == OSPREY_OK, "recovery analyze ok");
    CHECK(osprey_model(ctx) != NULL, "model installed after recovery");
    CHECK(g_reject_rows == 1, "only the first rejection logged");

    osprey_free(ctx);
    g_free(bad);
    g_free(good);
}

/* ------------------------------------------------------------------ */
/* Analysis-stage rejections                                           */
/* ------------------------------------------------------------------ */

static void test_variable_cap_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    c.max_variables = 1;
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    fill_two_access_facts(run);
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");

    OspreyStatus st = osprey_analyze(ctx);
    CHECK(st == OSPREY_LIMIT_EXCEEDED, "variable cap status");
    CHECK(osprey_tx_status(ctx) == OSPREY_LIMIT_EXCEEDED,
          "variable cap tx status");
    CHECK(strcmp(osprey_tx_stage(ctx), "closure") == 0,
          "variable cap tx stage");
    CHECK(osprey_model(ctx) == NULL, "variable cap no model");
    CHECK(g_reject_rows == 1, "variable cap one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_factor_cap_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    c.max_factors = 1;
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    fill_two_access_facts(run);
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");

    OspreyStatus st = osprey_analyze(ctx);
    CHECK(st == OSPREY_LIMIT_EXCEEDED, "factor cap status");
    CHECK(osprey_tx_status(ctx) == OSPREY_LIMIT_EXCEEDED,
          "factor cap tx status");
    CHECK(strcmp(osprey_tx_stage(ctx), "closure") == 0,
          "factor cap tx stage");
    CHECK(osprey_model(ctx) == NULL, "factor cap no model");
    CHECK(g_reject_rows == 1, "factor cap one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_empty_graph_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c); /* no facts at all */
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "empty merge ok");

    OspreyStatus st = osprey_analyze(ctx);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "empty graph status");
    CHECK(osprey_tx_status(ctx) == OSPREY_INCOMPLETE_FACTS,
          "empty graph tx status");
    CHECK(strcmp(osprey_tx_stage(ctx), "infer") == 0,
          "empty graph tx stage");
    CHECK(osprey_model(ctx) == NULL, "empty graph no model");
    CHECK(g_reject_rows == 1, "empty graph one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_exact_component_cap_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    c.max_exact_clique_vars = 1;
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    fill_two_access_facts(run);
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");

    OspreyStatus st = osprey_analyze(ctx);
    CHECK(st == OSPREY_EXACT_COMPONENT_TOO_LARGE, "exact cap status");
    CHECK(strcmp(osprey_tx_stage(ctx), "infer") == 0,
          "exact cap tx stage");
    CHECK(osprey_model(ctx) == NULL, "exact cap no model");
    CHECK(g_reject_rows == 1, "exact cap one reject row");

    osprey_free(ctx);
    g_free(run);
}

static void test_decoder_cap_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    ctx->graph = osprey_graph_new();
    for (uint32_t i = 0; i < 513; i++) {
        OspreyVar v;
        memset(&v, 0, sizeof(v));
        v.id = i;
        v.kind = OSPREY_PRED_ARRAY;
        v.belief = 1.0;
        v.payload.segment.a1.region.kind = OSPREY_REGION_GLOBAL;
        v.payload.segment.a1.offset = (int64_t)i * 16;
        v.payload.segment.a2 = v.payload.segment.a1;
        v.payload.segment.a2.offset += 8;
        v.payload.segment.size = 8;
        g_array_append_val(ctx->graph->vars, v);
    }
    osprey_tx_begin(ctx);
    OspreyStatus st = osprey_decode(ctx);
    CHECK(st == OSPREY_LIMIT_EXCEEDED, "decoder cap status");
    CHECK(ctx->staged_model == NULL, "decoder cap frees staged model");
    osprey_tx_reject(ctx, st, "decode", "decoder limit exceeded");
    CHECK(osprey_model(ctx) == NULL, "decoder cap no model");
    CHECK(g_reject_rows == 1, "decoder cap one reject row");

    osprey_free(ctx);
}

/* ------------------------------------------------------------------ */
/* Stage-1 identity, normalization, lifecycle                          */
/* ------------------------------------------------------------------ */

/* Two chunks that collide under the old packed key scheme (site delta
 * 2<<16 vs offset delta 1<<16 XOR-align) must be distinct under
 * full-field keys. */
static void test_key_collision_fixtures(void)
{
    OspreyChunk a, b;
    memset(&a, 0, sizeof(a));
    a.address.region.kind = OSPREY_REGION_GLOBAL;
    a.address.region.site_offset = 0x10000;
    a.address.offset = 0;
    a.size = 8;
    memset(&b, 0, sizeof(b));
    b.address.region.kind = OSPREY_REGION_GLOBAL;
    b.address.region.site_offset = 0x10002;
    b.address.offset = 0x10000;
    b.size = 8;

    OspreyKey ka = osprey_chunk_key(&a);
    OspreyKey kb = osprey_chunk_key(&b);
    CHECK(!osprey_key_equal(&ka, &kb), "colliding chunks distinct keys");

    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    ctx->graph = osprey_graph_new();
    OspreyVarPayload pa, pb;
    memset(&pa, 0, sizeof(pa)); pa.chunk = a;
    memset(&pb, 0, sizeof(pb)); pb.chunk = b;
    uint32_t va = osprey_intern_var_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pa);
    uint32_t vb = osprey_intern_var_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pb);
    CHECK(va != UINT32_MAX && vb != UINT32_MAX, "intern both chunks");
    CHECK(va != vb, "colliding chunks distinct vars");

    /* Attached predicates must include the complete target/base region,
     * not just its kind and image id. */
    OspreyVarPayload fa, fb;
    memset(&fa, 0, sizeof(fa));
    fa.attached.chunk = a;
    fa.attached.base.region.kind = OSPREY_REGION_HEAP_SITE;
    fa.attached.base.region.site_offset = 0x111;
    fa.attached.base.offset = 4;
    fb = fa;
    fb.attached.base.region.site_offset = 0x222;
    uint32_t vfa = osprey_intern_var_id(ctx, OSPREY_PRED_FIELD_OF, &fa);
    uint32_t vfb = osprey_intern_var_id(ctx, OSPREY_PRED_FIELD_OF, &fb);
    CHECK(vfa != vfb, "field bases at different sites remain distinct");

    /* HomoSegment identity includes both regions, not only a1 and the
     * numeric a2 offset. */
    OspreyVarPayload sa, sb;
    memset(&sa, 0, sizeof(sa));
    sa.segment.a1.region.kind = OSPREY_REGION_GLOBAL;
    sa.segment.a1.offset = 0x10;
    sa.segment.a2.region.kind = OSPREY_REGION_HEAP_SITE;
    sa.segment.a2.region.site_offset = 0x333;
    sa.segment.a2.offset = 0x20;
    sa.segment.size = 8;
    sb = sa;
    sb.segment.a2.region.site_offset = 0x444;
    uint32_t vsa = osprey_intern_var_id(ctx, OSPREY_PRED_HOMO_SEGMENT, &sa);
    uint32_t vsb = osprey_intern_var_id(ctx, OSPREY_PRED_HOMO_SEGMENT, &sb);
    CHECK(vsa != vsb, "segment partner regions remain distinct");
    osprey_free(ctx);
}

/* Bidirectional rules (A→B and B→A) must not dedup-collapse; polarity
 * and head index are part of the factor identity. */
static void test_factor_key_bidirectional(void)
{
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    ctx->graph = osprey_graph_new();
    OspreyVarPayload pa, pb;
    memset(&pa, 0, sizeof(pa));
    pa.chunk.address.region.kind = OSPREY_REGION_GLOBAL;
    pa.chunk.address.offset = 0;
    pa.chunk.size = 8;
    memset(&pb, 0, sizeof(pb));
    pb.chunk.address.region.kind = OSPREY_REGION_GLOBAL;
    pb.chunk.address.offset = 8;
    pb.chunk.size = 8;
    uint32_t va = osprey_intern_var_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pa);
    uint32_t vb = osprey_intern_var_id(ctx, OSPREY_PRED_PRIMITIVE_VAR, &pb);
    CHECK(va != UINT32_MAX && vb != UINT32_MAX, "intern factor vars");
    uint32_t ids[2] = { vb, va };
    osprey_factor_add(ctx, OSPREY_RULE_CA02, 0, false, 0.8, ids, 2);
    osprey_factor_add(ctx, OSPREY_RULE_CA02, 1, false, 0.8, ids, 2);
    CHECK(ctx->graph->factors->len == 2, "bidirectional factors distinct");
    osprey_factor_add(ctx, OSPREY_RULE_CA02, 0, false, 0.8, ids, 2);
    CHECK(ctx->graph->factors->len == 2, "duplicate factor deduped");
    osprey_factor_add(ctx, OSPREY_RULE_CA02, 0, true, 0.8, ids, 2);
    CHECK(ctx->graph->factors->len == 3, "polarity distinct");
    /* 0.5 and 1.0 have identical low 32 mantissa bits on IEEE-754.
     * Exact probability identity must retain all 64 bits. */
    osprey_factor_add(ctx, OSPREY_RULE_CA02, 0, false, 0.5, ids, 2);
    osprey_factor_add(ctx, OSPREY_RULE_CA02, 0, false, 1.0, ids, 2);
    CHECK(ctx->graph->factors->len == 5, "full probability bits distinct");
    osprey_free(ctx);
}

/* PC normalization at fact creation + merged global interval set with
 * image-relative offsets. */
static void test_pc_normalization_and_global_merge(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);

    osprey_set_image_bounds(0x400000, 0x401000);
    osprey_register_image_global(NULL, 0x402000, 0x1000); /* .data */
    osprey_register_image_global(NULL, 0x403000, 0x800);  /* .bss */
    osprey_child_use_shared_run(ctx, run);

    CPUArchState *env = g_malloc0(sizeof(CPUArchState));

    /* in-image access: pc 0x400100 -> 0x100, addr in .data */
    osprey_on_mem_access(env, 0x402008, 8, 0x400100, 0);
    /* out-of-image access (libc): skipped entirely */
    osprey_on_mem_access(env, 0x402010, 8, 0x7f0000001234, 0);
    /* .bss access resolves to the same canonical G region */
    osprey_on_mem_access(env, 0x403010, 4, 0x400200, 1);

    OspreyRegionId r;
    int64_t off;
    CHECK(osprey_region_of_addr(env, 0x402008, &r, &off, false),
          "data addr resolves");
    CHECK(r.kind == OSPREY_REGION_GLOBAL && off == 0x2008,
          "data addr image-relative offset");
    CHECK(osprey_region_of_addr(env, 0x403010, &r, &off, false),
          "bss addr resolves");
    CHECK(r.kind == OSPREY_REGION_GLOBAL && off == 0x3010,
          "bss addr image-relative offset");
    CHECK(!osprey_region_of_addr(env, 0x7f0000000000, &r, &off, false),
          "libc addr not resolved");

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");
    CHECK(ctx->access_facts->len == 2, "only in-image accesses recorded");
    OspreyAccessFact *f0 = &g_array_index(ctx->access_facts,
                                          OspreyAccessFact, 0);
    OspreyAccessFact *f1 = &g_array_index(ctx->access_facts,
                                          OspreyAccessFact, 1);
    CHECK(f0->pc == 0x100 && f1->pc == 0x200, "pcs normalized");
    CHECK(f0->chunk.address.offset == 0x2008 &&
          f1->chunk.address.offset == 0x3010, "offsets image-relative");
    CHECK(f0->chunk.address.region.kind == OSPREY_REGION_GLOBAL &&
          f1->chunk.address.region.kind == OSPREY_REGION_GLOBAL,
          "both accesses in G");
    CHECK(ctx->region_instances->len == 1, "one merged global instance");
    OspreyRegionInstance *gi = &g_array_index(ctx->region_instances,
                                              OspreyRegionInstance, 0);
    CHECK(gi->raw_base == 0x400000, "global raw base = image base");
    CHECK(gi->instance_id == 0, "global instance uses reserved id");
    CHECK(gi->raw_min == 0x400000 && gi->raw_max == 0x403800,
          "global observed bounds reach highest image offset");

    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

/* Heap lifecycle: provenance identity, same-base reuse, retire by
 * identity, stale-origin rejection. */
static void test_heap_identity_lifecycle(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    osprey_set_image_bounds(0x400000, 0x401000);
    osprey_child_use_shared_run(ctx, run);

    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    provenance_init();

    PtrTag t1 = provenance_create_object(0x1000, 32, 0x400200,
                                          PROV_PRODUCER_MALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_MALLOC,
            .site_pc = 0x400200,
            .requested_size = 32,
        };
        osprey_on_alloc_success(env, &obs, 0x1000, t1.object_id, t1.generation);
    }

    /* same-base reuse: retire t1, allocate again at the same base */
    osprey_on_free_identity(env, t1.object_id, t1.generation, 0x400300);
    provenance_retire_object(0x1000);
    PtrTag t2 = provenance_create_object(0x1000, 64, 0x400200,
                                          PROV_PRODUCER_MALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_MALLOC,
            .site_pc = 0x400200,
            .requested_size = 64,
        };
        osprey_on_alloc_success(env, &obs, 0x1000, t2.object_id, t2.generation);
    }

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");
    CHECK(ctx->region_instances->len == 2, "two instances at same base");
    OspreyRegionInstance *h0 = &g_array_index(ctx->region_instances,
                                              OspreyRegionInstance, 0);
    OspreyRegionInstance *h1 = &g_array_index(ctx->region_instances,
                                              OspreyRegionInstance, 1);
    CHECK(h0->prov_object_id != h1->prov_object_id,
          "instances carry distinct provenance ids");
    CHECK(h0->instance_id != h1->instance_id,
          "instances carry distinct runtime ids");

    OspreyRegionId r;
    int64_t off;
    CHECK(osprey_region_of_addr(env, 0x1000, &r, &off, false),
          "live instance resolves");
    CHECK(r.kind == OSPREY_REGION_HEAP_SITE && off == 0,
          "heap region + offset");

    /* origin validation: freed identity rejected, live accepted */
    OspreyAddressOrigin o;
    memset(&o, 0, sizeof(o));
    o.valid = 1;
    o.width = sizeof(target_ulong);
    o.prov_object_id = t1.object_id;
    o.prov_generation = t1.generation;
    o.concrete_value = 0x1000;
    o.canonical.region.kind = OSPREY_REGION_HEAP_SITE;
    o.canonical.region.site_offset = 0x200;
    o.canonical.offset = 0;
    CHECK(!osprey_address_origin_live(&o), "freed identity rejected");
    o.prov_object_id = t2.object_id;
    o.prov_generation = t2.generation;
    CHECK(osprey_address_origin_live(&o), "live identity accepted");
    o.concrete_value = 0x1000 + 64; /* past end */
    CHECK(!osprey_address_origin_live(&o), "out-of-bounds value rejected");

    /* The lifecycle API accepts only the authoritative identity. */
    osprey_on_free_identity(env, t2.object_id, t2.generation, 0x400400);
    CHECK(!osprey_region_of_addr(env, 0x1000, &r, &off, false),
          "freed instance no longer resolves");

    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

/* Deterministic allocator lifecycle variants.  These drive the same
 * accepted provenance/OSPREY event order as the modeled realloc return
 * hook without relying on glibc placement choices. */
static void test_realloc_lifecycle_variants(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    osprey_set_image_bounds(0x400000, 0x401000);
    osprey_child_use_shared_run(ctx, run);

    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    provenance_init();
    OspreyRegionId r;
    int64_t off;

    PtrTag old = provenance_create_object(0x2000, 16, 0x400210,
                                           PROV_PRODUCER_MALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_MALLOC,
            .site_pc = 0x400210,
            .requested_size = 16,
        };
        osprey_on_alloc_success(env, &obs, 0x2000, old.object_id, old.generation);
    }

    /* Failed realloc publishes only the failure observation; the old
     * provenance identity and OSPREY runtime instance remain live. */
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_REALLOC,
            .site_pc = 0x400220,
        };
        osprey_on_alloc_failure(&obs);
    }
    CHECK(osprey_region_of_addr(env, 0x2000, &r, &off, false),
          "failed realloc preserves old instance");

    /* Successful in-place realloc: retire old identity first, then create
     * a new generation at the same numeric base and new allocation site. */
    osprey_on_free_identity(env, old.object_id, old.generation, 0x400230);
    provenance_retire_object(0x2000);
    PtrTag same = provenance_create_object(0x2000, 64, 0x400230,
                                            PROV_PRODUCER_REALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_REALLOC,
            .site_pc = 0x400230,
            .requested_size = 64,
        };
        osprey_on_alloc_success(env, &obs, 0x2000, same.object_id, same.generation);
    }
    CHECK(osprey_region_of_addr(env, 0x203f, &r, &off, false) && off == 63,
          "in-place realloc installs new extent");
    CHECK(same.object_id != old.object_id,
          "in-place realloc uses a new provenance identity");

    /* Successful moved realloc: old same-base generation is retired and
     * only the new numeric base resolves. */
    osprey_on_free_identity(env, same.object_id, same.generation, 0x400240);
    provenance_retire_object(0x2000);
    PtrTag moved = provenance_create_object(0x3000, 128, 0x400240,
                                             PROV_PRODUCER_REALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_REALLOC,
            .site_pc = 0x400240,
            .requested_size = 128,
        };
        osprey_on_alloc_success(env, &obs, 0x3000, moved.object_id, moved.generation);
    }
    CHECK(!osprey_region_of_addr(env, 0x2000, &r, &off, false),
          "moved realloc retires old numeric base");
    CHECK(osprey_region_of_addr(env, 0x307f, &r, &off, false) && off == 127,
          "moved realloc installs destination extent");

    /* realloc(p,0) with NULL return retires without replacement. */
    osprey_on_free_identity(env, moved.object_id, moved.generation, 0x400250);
    provenance_retire_object(0x3000);
    CHECK(!osprey_region_of_addr(env, 0x3000, &r, &off, false),
          "realloc zero retires old instance");

    /* A successful zero-size non-NULL result remains a distinct runtime
     * instance with an empty half-open span. */
    PtrTag zero = provenance_create_object(0x4000, 0, 0x400260,
                                            PROV_PRODUCER_REALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_REALLOC,
            .site_pc = 0x400260,
            .requested_size = 0,
        };
        osprey_on_alloc_success(env, &obs, 0x4000, zero.object_id, zero.generation);
    }

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");
    int same_base_rows = 0;
    int zero_rows = 0;
    for (guint i = 0; i < ctx->region_instances->len; i++) {
        OspreyRegionInstance *ri = &g_array_index(
            ctx->region_instances, OspreyRegionInstance, i);
        if (ri->raw_base == 0x2000) {
            same_base_rows++;
        }
        if (ri->raw_base == 0x4000 && ri->raw_min == ri->raw_max) {
            zero_rows++;
        }
    }
    CHECK(same_base_rows == 2,
          "in-place realloc preserves two distinct lifecycle rows");
    CHECK(zero_rows == 1, "zero-size success records empty instance");
    /* Failed realloc is a diagnostic, not a fact: no alloc row at the
     * failure site, and the old identity stayed live. */
    bool saw_failure_fact = false;
    for (guint i = 0; i < ctx->alloc_facts->len; i++) {
        OspreyMallocFact *f = &g_array_index(ctx->alloc_facts,
                                             OspreyMallocFact, i);
        if (f->site_pc == 0x220) {
            saw_failure_fact = true;
        }
    }
    CHECK(!saw_failure_fact, "failed realloc publishes no alloc fact");

    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

/* Stack frames: entry_sp convention, imprecise-frame exclusion, RSP
 * origin seeding and re-derivation. */
static void test_stack_frames_and_rsp_origin(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    osprey_set_image_bounds(0x400000, 0x401000);
    osprey_child_use_shared_run(ctx, run);

    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    OspreyCpuOriginState *st = osprey_cpu_origin(env);

    /* imprecise callee (libc) as the only frame: no seed, window not
     * resolvable, ret pops it */
    osprey_on_call(env, 0x7f0000000000, 0x7ffbfff8);
    CHECK(!st->regs[R_ESP].address.valid, "imprecise call leaves rsp origin invalid");
    OspreyRegionId r;
    int64_t off;
    CHECK(!osprey_region_of_addr(env, 0x7ffbff00, &r, &off, false),
          "imprecise frame window not resolvable");
    osprey_on_ret(env, 0x7f0000000001, 0x7ffc0000);
    CHECK(!st->regs[R_ESP].address.valid, "no frames -> rsp origin invalid");

    /* precise callee: entry_sp = 0x7ffc0000, origin at offset 0 */
    osprey_on_call(env, 0x400500, 0x7ffc0000);
    CHECK(st->regs[R_ESP].address.valid &&
          st->regs[R_ESP].address.width == sizeof(target_ulong),
          "rsp origin seeded at call");
    CHECK(st->regs[R_ESP].address.canonical.offset == 0,
          "rsp origin offset 0");
    CHECK(st->regs[R_ESP].address.canonical.region.site_offset == 0x500,
          "rsp origin frame site");

    /* rsp update below entry (prologue push): signed offset */
    osprey_on_rsp_update(env, 0x7ffbfff0, 0x400501);
    CHECK(st->regs[R_ESP].address.valid &&
          st->regs[R_ESP].address.canonical.offset == -16,
          "rsp update keeps frame origin with signed offset");
    /* out-of-image rsp write invalidates */
    osprey_on_rsp_update(env, 0x7ffbffe0, 0x7f0000001234);
    CHECK(!st->regs[R_ESP].address.valid, "out-of-image rsp write invalidates");
    osprey_on_rsp_update(env, 0x7ffbfff0, 0x400501);
    CHECK(st->regs[R_ESP].address.valid, "in-image rsp write re-derives");

    /* An imprecise nested call invalidates the precise caller's RSP
     * origin while library code runs; its RET restores the caller. */
    osprey_on_call(env, 0x7f0000000000, 0x7ffbffe8);
    CHECK(!st->regs[R_ESP].address.valid,
          "imprecise nested call invalidates caller rsp origin");
    osprey_on_ret(env, 0x400501, 0x7ffbfff0);
    CHECK(st->regs[R_ESP].address.valid &&
          st->regs[R_ESP].address.canonical.region.site_offset == 0x500,
          "library return restores precise caller");

    /* A normal nested return selects the caller; the callee must not
     * claim the caller's post-pop RSP. */
    osprey_on_call(env, 0x400600, 0x7ffbffe8);
    osprey_on_ret(env, 0x400601, 0x7ffbfff0);
    CHECK(st->regs[R_ESP].address.valid &&
          st->regs[R_ESP].address.canonical.region.site_offset == 0x500,
          "normal return resolves to caller");

    /* ret pops the frame; no frames left -> invalid */
    osprey_on_ret(env, 0x400501, 0x7ffc0008);
    CHECK(!st->regs[R_ESP].address.valid, "rsp origin invalid after final ret");

    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

/* Canonical dump: written after a successful merge, sorted rows. */
static void test_canonical_dump(void)
{
    reset_log();
    OspreyConfig c = test_config();
    snprintf(c.dump_file, sizeof(c.dump_file), "/tmp/osprey_dump_test.txt");
    unlink(c.dump_file);
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    fill_two_access_facts(run);
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "dump merge ok");
    FILE *f = fopen(c.dump_file, "r");
    CHECK(f != NULL, "dump file written");
    if (f != NULL) {
        char line[256];
        int access_rows = 0;
        while (fgets(line, sizeof(line), f)) {
            if (strncmp(line, "access ", 7) == 0) access_rows++;
        }
        fclose(f);
        CHECK(access_rows == 2, "dump has two access rows");
    }
    unlink(c.dump_file);
    osprey_free(ctx);
    g_free(run);
}

/* Entrypoint frame seeding: a main-image function reached from
 * uninstrumented loader/libc code has no call hook; the entrypoint
 * barrier seeds a precise frame at the observed entry SP. */
static void test_entrypoint_frame_seeding(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    osprey_set_image_bounds(0x400000, 0x401000);
    osprey_child_use_shared_run(ctx, run);

    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    OspreyCpuOriginState *st = osprey_cpu_origin(env);

    /* Seed main's frame at the observed entry SP. */
    osprey_on_entrypoint(env, 0x400100, 0x7ffc0000);
    CHECK(st->regs[R_ESP].address.valid &&
          st->regs[R_ESP].address.width == sizeof(target_ulong),
          "entrypoint seeds rsp origin");
    CHECK(st->regs[R_ESP].address.canonical.offset == 0,
          "entrypoint origin at offset zero");
    CHECK(st->regs[R_ESP].address.canonical.region.site_offset == 0x100,
          "entrypoint origin frame site");

    /* A real prologue establishes the observed lower bound before local
     * addresses are resolved. */
    osprey_on_rsp_update(env, 0x7ffbff00, 0x400101);
    OspreyRegionId r;
    int64_t off;
    CHECK(osprey_region_of_addr(env, 0x7ffbff00, &r, &off, false),
          "entrypoint frame window resolves");
    CHECK(r.kind == OSPREY_REGION_STACK_FUNCTION &&
          r.site_offset == 0x100 && off == -0x100,
          "entrypoint frame region + signed offset");

    /* Idempotent: a second hit with the same region + entry SP creates
     * no second frame. */
    osprey_on_entrypoint(env, 0x400100, 0x7ffc0000);

    /* Called-patch case: the ordinary call hook already created the
     * exact frame.  The barrier must reuse it and restore its origin,
     * not append a duplicate runtime instance. */
    osprey_on_rsp_update(env, 0x7ffbfff8, 0x400100);
    osprey_on_call(env, 0x400200, 0x7ffbfff8);
    osprey_on_reg_invalidate(env, R_ESP);
    osprey_on_entrypoint(env, 0x400200, 0x7ffbfff8);
    CHECK(st->regs[R_ESP].address.valid &&
          st->regs[R_ESP].address.canonical.region.site_offset == 0x200,
          "called-patch barrier restores existing frame origin");

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");
    int frames = 0;
    int called_patch_frames = 0;
    for (guint i = 0; i < ctx->region_instances->len; i++) {
        OspreyRegionInstance *ri = &g_array_index(
            ctx->region_instances, OspreyRegionInstance, i);
        if (ri->region.kind == OSPREY_REGION_STACK_FUNCTION &&
            ri->region.site_offset == 0x100) {
            frames++;
        }
        if (ri->region.kind == OSPREY_REGION_STACK_FUNCTION &&
            ri->region.site_offset == 0x200) {
            called_patch_frames++;
        }
    }
    CHECK(frames == 1, "entrypoint seeding is idempotent");
    CHECK(called_patch_frames == 1,
          "called-patch entrypoint does not duplicate frame");

    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

/* Non-local stack resynchronization: longjmp-style RSP replacement and
 * RSP writes above the top frame pop stale frames; mismatched-return
 * near misses pop nothing. */
static void test_stack_resync(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    osprey_set_image_bounds(0x400000, 0x401000);
    osprey_child_use_shared_run(ctx, run);

    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    OspreyCpuOriginState *st = osprey_cpu_origin(env);

    /* main -> f1 -> f2 nested frames. */
    osprey_on_entrypoint(env, 0x400100, 0x7ffc0000);
    osprey_on_call(env, 0x400200, 0x7ffbfff8);
    osprey_on_call(env, 0x400300, 0x7ffbfff0);

    /* longjmp: in-image RSP write back into main's frame.  The stale
     * f1/f2 frames cannot contain the new SP and are popped; main
     * survives as the owner. */
    osprey_on_rsp_update(env, 0x7ffbfffc, 0x400100);
    CHECK(st->regs[R_ESP].address.valid &&
          st->regs[R_ESP].address.canonical.region.site_offset == 0x100,
          "longjmp rsp write resolves to surviving main frame");
    CHECK(st->regs[R_ESP].address.canonical.offset == -4,
          "longjmp rsp write seeds main at signed offset");
    OspreyRegionId r;
    int64_t off;
    CHECK(osprey_region_of_addr(env, 0x7ffbffe0, &r, &off, false),
          "stale f1 window no longer claims addresses");
    CHECK(r.site_offset == 0x100, "f1 window address resolves to main");

    /* RSP write above the top frame (stack switch / unwind): pops
     * everything, no owner -> invalidate. */
    osprey_on_call(env, 0x400400, 0x7ffbffc0);
    osprey_on_rsp_update(env, 0x7ffd0000, 0x400401);
    CHECK(!st->regs[R_ESP].address.valid, "rsp above all frames invalidates");

    /* Mismatched-return near miss: RET always pops the callee, but a
     * post-pop SP still inside the caller's exact window must not pop
     * the caller as well. */
    osprey_on_entrypoint(env, 0x400100, 0x7ffc2000);
    osprey_on_rsp_update(env, 0x7ffc1ff8, 0x400100);
    osprey_on_call(env, 0x400500, 0x7ffc1ff8);
    osprey_on_ret(env, 0x400501, 0x7ffc1ff8);
    CHECK(st->regs[R_ESP].address.valid &&
          st->regs[R_ESP].address.canonical.region.site_offset == 0x100,
          "near-miss ret keeps the caller frame");
    CHECK(st->regs[R_ESP].address.canonical.offset == -8,
          "near-miss ret restores caller signed offset");

    osprey_on_call(env, 0x400500, 0x7ffc1ff0);

    /* Recursion cleanup: one ret with sp above all stale frames pops
     * the whole stale chain. */
    osprey_on_call(env, 0x400600, 0x7ffc1fe8);
    osprey_on_call(env, 0x400600, 0x7ffc1fe0);
    osprey_on_ret(env, 0x400601, 0x7ffc1ff0);
    CHECK(st->regs[R_ESP].address.valid &&
          st->regs[R_ESP].address.canonical.region.site_offset == 0x500,
          "ret above stale chain pops to surviving owner");

    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

/* Observed stack bounds: the shared record tracks {entry_sp, min_sp,
 * max_sp} and merges as the frame grows; the canonical dump extent is
 * the observed span, not a synthetic 1 MiB. */
static void test_observed_stack_bounds(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    osprey_set_image_bounds(0x400000, 0x401000);
    osprey_child_use_shared_run(ctx, run);

    CPUArchState *env = g_malloc0(sizeof(CPUArchState));

    osprey_on_entrypoint(env, 0x400100, 0x7ffc0000);
    /* A proven prologue RSP write more than one MiB below entry remains
     * in the current frame; there is no synthetic depth window. */
    osprey_on_rsp_update(env, 0x7feb0000, 0x400101);
    /* A red-zone access grows the observed bound by exactly 128 bytes. */
    OspreyRegionId r;
    int64_t off;
    CHECK(osprey_region_of_addr(env, 0x7feaff80, &r, &off, false),
          "red-zone access resolves");
    CHECK(off == -0x110080, "deep access signed offset");
    CHECK(!osprey_region_of_addr(env, 0x7feafe00, &r, &off, false),
          "address below red zone is not guessed into frame");

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");
    OspreyRegionInstance *ri = NULL;
    for (guint i = 0; i < ctx->region_instances->len; i++) {
        OspreyRegionInstance *cand = &g_array_index(
            ctx->region_instances, OspreyRegionInstance, i);
        if (cand->region.kind == OSPREY_REGION_STACK_FUNCTION &&
            cand->region.site_offset == 0x100) {
            ri = cand;
            break;
        }
    }
    CHECK(ri != NULL, "frame instance recorded");
    if (ri != NULL) {
        CHECK(ri->raw_base == 0x7ffc0000, "frame raw base = entry sp");
        CHECK(ri->raw_min == 0x7feaff80, "frame raw_min = deepest access");
        CHECK(ri->raw_max == 0x7ffc0000, "frame raw_max = entry sp");
        CHECK(ri->raw_max - ri->raw_min == 0x110080,
              "frame observed span, not synthetic 1 MiB");
    }

    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

/* ------------------------------------------------------------------ */
/* Stage 2.1: sample composition, Boolean support, caps, saturation    */
/* ------------------------------------------------------------------ */

/* Build a canonical access fact (global region, image-relative offset). */
static void fill_access_fact(OspreyAccessFact *f, uint64_t pc,
                             int64_t offset, uint64_t size,
                             uint32_t dynamic) {
    memset(f, 0, sizeof(*f));
    f->pc = pc;
    f->chunk.address.region.kind = OSPREY_REGION_GLOBAL;
    f->chunk.address.region.site_offset = 0;
    f->chunk.address.offset = offset;
    f->chunk.size = size;
    f->dynamic_count = dynamic;
    f->sample_support = 1;
    f->is_store = 0;
}

/* The baseline sample is `prefix ∪ child-suffix`: freeze the prefix,
 * then a child suffix that re-observes one prefix fact and adds a new
 * one.  The union must commit exactly once (support 1, never 2), the
 * dynamic total must be the exact sum, and the per-sample unique-fact
 * count must not double-count prefix facts. */
static void test_prefix_suffix_composition(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);

    OspreyAccessFact f1, f2, f3, f4;
    OspreyBaseFact b1;
    fill_access_fact(&f1, 0x100, 0, 8, 1);
    fill_access_fact(&f2, 0x200, 8, 8, 1);
    CHECK(osprey_table_insert_access(run, &f1) == 1, "prefix insert f1");
    CHECK(osprey_table_insert_access(run, &f2) == 1, "prefix insert f2");
    memset(&b1, 0, sizeof(b1));
    b1.pc = f1.pc;
    b1.chunk = f1.chunk;
    b1.base = f1.chunk.address;
    b1.sample_support = 1;
    CHECK(osprey_table_insert_base(run, &b1) == 1,
          "prefix base fact reuses f1 chunk");
    run->total_dynamic_observations = 2;   /* child-side counter */
    CHECK(run->total_facts_count == 3, "prefix facts counted");
    CHECK(run->census_chunk_used == 2,
          "cross-family duplicate chunk counted once");

    CHECK(osprey_shared_run_freeze_prefix(ctx, run), "prefix freeze");
    CHECK(run->prefix_frozen == 1, "prefix frozen flag");
    CHECK(osprey_run_prefix_used(run, OSPREY_TABLE_PREFIX_ACCESS) == 2,
          "prefix family holds two access facts");
    CHECK(run->access_used == 0, "suffix starts empty");
    CHECK(run->total_dynamic_prefix == 2, "prefix dynamic total frozen");
    CHECK(run->total_dynamic_observations == 0, "suffix dynamic reset");
    CHECK(osprey_shared_run_freeze_prefix(ctx, run),
          "freeze is idempotent success");

    /* Child suffix: re-observe f1 twice, add f3. */
    fill_access_fact(&f1, 0x100, 0, 8, 2);
    fill_access_fact(&f3, 0x300, 16, 8, 1);
    CHECK(osprey_table_insert_access(run, &f1) == 1, "child dup f1");
    CHECK(osprey_table_insert_access(run, &f3) == 1, "child new f3");
    run->total_dynamic_observations = 3;
    CHECK(run->total_facts_count == 4,
          "unique-fact count is the union, prefix not re-counted");
    CHECK(run->census_chunk_used == 3, "census covers union chunks");

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "compose merge");
    CHECK(ctx->access_facts->len == 3, "three facts merged");
    CHECK(ctx->base_facts->len == 1, "one base fact merged");
    CHECK(ctx->total_samples == 1, "one sample committed");
    CHECK(ctx->total_dynamic_observations == 5,
          "dynamic total = prefix 2 + child 3");
    OspreyAccessFact *m1 = NULL;
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *cand = &g_array_index(ctx->access_facts,
                                                OspreyAccessFact, i);
        if (cand->pc == 0x100) {
            m1 = cand;
        }
    }
    CHECK(m1 != NULL, "prefix/suffix-shared fact merged");
    if (m1 != NULL) {
        CHECK(m1->sample_support == 1,
              "shared fact support once per sample (never 2)");
        CHECK(m1->dynamic_count == 3, "shared fact sums prefix + child");
    }

    /* Sample 2 (child-only): prepare keeps the frozen prefix and the
     * per-sample census; the new sample commits exactly one fact and
     * re-committed facts gain one support per unique sample. */
    osprey_shared_run_prepare(ctx, run, 1);
    CHECK(run->prefix_frozen == 1, "prepare keeps the prefix");
    CHECK(osprey_run_prefix_used(run, OSPREY_TABLE_PREFIX_ACCESS) == 2,
          "prefix survives prepare");
    CHECK(run->access_used == 0, "suffix zeroed by prepare");
    CHECK(run->total_facts_count == 3,
          "prepare restores frozen-prefix fact count");
    CHECK(run->census_chunk_used == 2, "census rebuilt from prefix");
    OspreyCensusRegion *global_census = NULL;
    {
        OspreyRunIter it;
        const void *rec;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = OSPREY_TABLE_CENSUS_REGION;
        while (osprey_run_iter_next(&it, &rec)) {
            OspreyCensusRegion *candidate = (OspreyCensusRegion *)rec;
            if (candidate->region.kind == OSPREY_REGION_GLOBAL) {
                global_census = candidate;
                break;
            }
        }
    }
    CHECK(global_census != NULL && global_census->chunk_count == 2,
          "census rebuild counts unique chunks, not fact occurrences");
    fill_access_fact(&f4, 0x400, 24, 8, 1);
    CHECK(osprey_table_insert_access(run, &f4) == 1, "sample-2 child fact");
    run->total_dynamic_observations = 1;
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK,
          "sample-2 merge");
    CHECK(ctx->access_facts->len == 4, "sample 2 adds one fact");
    CHECK(ctx->total_samples == 2, "two samples committed");
    CHECK(ctx->total_dynamic_observations == 8,
          "sample 2 dynamic (2 prefix + 1 child) added");
    m1 = NULL;
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *cand = &g_array_index(ctx->access_facts,
                                                OspreyAccessFact, i);
        if (cand->pc == 0x100) {
            m1 = cand;
        }
    }
    CHECK(m1 != NULL && m1->sample_support == 2,
          "support is one per unique committed sample");

    osprey_free(ctx);
    g_free(run);
}

/* Child-only sample (no frozen prefix): the plain path resets the whole
 * run and the merged facts carry Boolean per-sample support. */
static void test_child_only_sample(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);

    OspreyAccessFact f;
    fill_access_fact(&f, 0x100, 0, 8, 1);
    CHECK(osprey_table_insert_access(run, &f) == 1, "child insert");
    run->total_dynamic_observations = 1;

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK,
          "child-only merge");
    CHECK(ctx->access_facts->len == 1, "one fact");
    CHECK(ctx->total_samples == 1, "one sample");
    OspreyAccessFact *m = &g_array_index(ctx->access_facts,
                                         OspreyAccessFact, 0);
    CHECK(m->sample_support == 1, "child-only support 1");
    CHECK(m->dynamic_count == 1, "child-only dynamic 1");

    osprey_free(ctx);
    g_free(run);
}

/* Repeated dynamic observations: a fact observed N times within one
 * sample keeps Boolean support and exact dynamic count. */
static void test_duplicate_dynamic_observation(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);

    OspreyAccessFact f;
    fill_access_fact(&f, 0x100, 0, 8, 1);
    CHECK(osprey_table_insert_access(run, &f) == 1, "first observation");
    CHECK(osprey_table_insert_access(run, &f) == 0, "second updates");
    CHECK(osprey_table_insert_access(run, &f) == 0, "third updates");
    run->total_dynamic_observations = 3;

    /* Read back the merged record from the run table (open addressing
     * places it by hash, not at slot 0). */
    OspreyAccessFact *in_run = NULL;
    {
        OspreyRunIter it;
        const void *rec;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = OSPREY_TABLE_ACCESS;
        while (osprey_run_iter_next(&it, &rec)) {
            const OspreyAccessFact *cand = rec;
            if (cand->pc == 0x100) {
                in_run = (OspreyAccessFact *)cand;
                break;
            }
        }
    }
    CHECK(in_run != NULL, "access fact present in run");
    if (in_run != NULL) {
        CHECK(in_run->dynamic_count == 3, "exact dynamic count in run");
        CHECK(in_run->sample_support == 1, "boolean support in run");
    }

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge");
    OspreyAccessFact *m = &g_array_index(ctx->access_facts,
                                         OspreyAccessFact, 0);
    CHECK(m->dynamic_count == 3, "exact dynamic count merged");
    CHECK(m->sample_support == 1, "boolean support merged");
    CHECK(ctx->total_dynamic_observations == 3, "exact dynamic total");

    osprey_free(ctx);
    g_free(run);
}

/* Checked/saturating counters: dynamic counts saturate at UINT32_MAX
 * (fact) and UINT64_MAX (sample total), never wrap. */
static void test_counter_saturation(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);

    OspreyAccessFact f;
    fill_access_fact(&f, 0x100, 0, 8, UINT32_MAX - 1);
    CHECK(osprey_table_insert_access(run, &f) == 1, "near-max observation");
    fill_access_fact(&f, 0x100, 0, 8, 1);
    CHECK(osprey_table_insert_access(run, &f) == 0, "overflow observation");
    run->total_dynamic_observations = UINT64_MAX - 1;
    OspreyAccessFact *seen = NULL;
    {
        OspreyRunIter it;
        const void *rec;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = OSPREY_TABLE_ACCESS;
        while (osprey_run_iter_next(&it, &rec)) {
            const OspreyAccessFact *cand = rec;
            if (cand->pc == 0x100) {
                seen = (OspreyAccessFact *)cand;
                break;
            }
        }
    }
    CHECK(seen != NULL, "fact present in run");
    if (seen != NULL) {
        CHECK(seen->dynamic_count == UINT32_MAX, "fact dynamic saturates");
    }

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge");
    CHECK(ctx->access_facts->len == 1, "one fact");
    OspreyAccessFact *m = &g_array_index(ctx->access_facts,
                                         OspreyAccessFact, 0);
    CHECK(m->dynamic_count == UINT32_MAX, "merged dynamic saturated");
    CHECK(ctx->total_dynamic_observations == UINT64_MAX - 1,
          "sample total near-max exact");

    /* Second sample pushes the sample total past UINT64_MAX. */
    OspreySharedRun *run2 = new_run(&c);
    fill_access_fact(&f, 0x100, 0, 8, 1);
    CHECK(osprey_table_insert_access(run2, &f) == 1, "sample-2 insert");
    run2->total_dynamic_observations = 2;
    ctx->total_samples = UINT64_MAX;
    CHECK(osprey_parent_merge_sample(ctx, run2) == OSPREY_OK,
          "sample-2 merge");
    CHECK(ctx->total_dynamic_observations == UINT64_MAX,
          "sample total saturates, never wraps");
    CHECK(ctx->total_samples == UINT64_MAX,
          "committed sample count saturates, never wraps");

    osprey_free(ctx);
    g_free(run);
    g_free(run2);
}

/* max_facts: a new unique fact beyond the per-sample unique-fact cap is
 * rejected before insertion; the merge fails closed with no partial
 * commit.  Duplicates never trip the cap. */
static void test_fact_cap_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    c.max_facts = 16;   /* below the 64-slot table floor: the cap is the
                         * binding limit, not the table capacity */
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);

    for (int i = 0; i < 16; i++) {
        OspreyAccessFact f;
        fill_access_fact(&f, 0x100 + i, i * 8, 8, 1);
        CHECK(osprey_table_insert_access(run, &f) == 1, "unique fact ok");
    }
    CHECK(run->total_facts_count == 16, "sixteen unique facts");
    CHECK(run->overflow == 0, "cap not exceeded yet");
    /* A duplicate observation at the cap is still accepted. */
    OspreyAccessFact dup;
    fill_access_fact(&dup, 0x100, 0, 8, 1);
    CHECK(osprey_table_insert_access(run, &dup) == 0,
          "duplicate at cap updates, not rejected");

    OspreyAccessFact f17;
    fill_access_fact(&f17, 0x110, 16 * 8, 8, 1);
    CHECK(osprey_table_insert_access(run, &f17) == -1, "cap rejects 17th");
    CHECK(run->overflow == 1, "fact-cap overflow sticky");
    CHECK(run->first_dropped_kind != 0, "drop kind recorded");

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_INCOMPLETE_FACTS,
          "fact cap merge rejects fail-closed");
    CHECK(ctx->access_facts->len == 0, "fact cap no partial merge");
    CHECK(g_reject_rows == 1, "fact cap one reject row");

    osprey_free(ctx);
    g_free(run);

    /* A child re-observation of a frozen-prefix fact is not a new union
     * member and remains legal when the prefix already fills max_facts. */
    reset_log();
    c.max_facts = 1;
    ctx = osprey_new(&c);
    run = new_run(&c);
    OspreyAccessFact prefix;
    fill_access_fact(&prefix, 0x200, 0, 8, 1);
    CHECK(osprey_table_insert_access(run, &prefix) == 1,
          "prefix fills fact cap");
    CHECK(osprey_shared_run_freeze_prefix(ctx, run),
          "fact-cap prefix freeze");
    osprey_shared_run_prepare(ctx, run, 1);
    CHECK(run->total_facts_count == 1, "prefix cap count restored");
    CHECK(osprey_table_insert_access(run, &prefix) == 1,
          "frozen duplicate accepted at cap");
    CHECK(osprey_table_insert_access(run, &prefix) == 0,
          "duplicate updates a physically full suffix table");
    CHECK(run->overflow == 0, "frozen duplicate does not overflow");
    CHECK(run->total_facts_count == 1,
          "frozen duplicate does not consume fact cap");
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK,
          "frozen duplicate at cap merges");
    CHECK(ctx->access_facts->len == 1 &&
          g_array_index(ctx->access_facts, OspreyAccessFact, 0)
                  .sample_support == 1 &&
          g_array_index(ctx->access_facts, OspreyAccessFact, 0)
                  .dynamic_count == 3,
          "frozen duplicates contribute one support and exact dynamics");
    osprey_free(ctx);
    g_free(run);
}

/* max_chunks_per_region: a region with more unique chunks than the
 * configured limit rejects the new chunk before insertion and the
 * merge fails closed-close. */
static void test_chunk_cap_rejection(void)
{
    reset_log();
    OspreyConfig c = test_config();
    c.max_chunks_per_region = 4;
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);

    for (int i = 0; i < 4; i++) {
        OspreyAccessFact f;
        fill_access_fact(&f, 0x100 + i, i * 8, 8, 1);
        CHECK(osprey_table_insert_access(run, &f) == 1, "chunk ok");
    }
    CHECK(run->overflow == 0, "within per-region limit");
    OspreyAccessFact f5;
    fill_access_fact(&f5, 0x104, 4 * 8, 8, 1);
    CHECK(osprey_table_insert_access(run, &f5) == -1, "5th chunk rejected");
    CHECK(run->overflow == 1, "chunk-cap overflow sticky");
    CHECK(run->first_dropped_kind == OSPREY_TABLE_CENSUS_REGION + 1,
          "region census recorded as dropped kind");

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_INCOMPLETE_FACTS,
          "chunk cap merge rejects fail-closed");
    CHECK(ctx->access_facts->len == 0, "chunk cap no partial merge");
    CHECK(g_reject_rows == 1, "chunk cap one reject row");

    osprey_free(ctx);
    g_free(run);
}

/* Mutation iterations never merge: after a baseline sample, a later
 * iteration's observations stay out of the committed facts; a
 * subsequent baseline sample commits only its own facts. */
static void test_mutation_run_isolated(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);

    OspreyAccessFact f1, f2, f3, f4;
    fill_access_fact(&f1, 0x100, 0, 8, 1);
    fill_access_fact(&f2, 0x200, 8, 8, 1);
    CHECK(osprey_table_insert_access(run, &f1) == 1, "prefix f1");
    CHECK(osprey_table_insert_access(run, &f2) == 1, "prefix f2");
    CHECK(osprey_shared_run_freeze_prefix(ctx, run), "freeze");
    fill_access_fact(&f3, 0x300, 16, 8, 1);
    CHECK(osprey_table_insert_access(run, &f3) == 1, "baseline child f3");
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK,
          "baseline sample 1");
    CHECK(ctx->access_facts->len == 3, "baseline 1 committed");
    CHECK(ctx->total_samples == 1, "baseline 1 samples");

    /* Mutation iteration: prepare + observations, never merged. */
    osprey_shared_run_prepare(ctx, run, 2);
    CHECK(run->total_facts_count == 2,
          "mutation prepare restores prefix fact count");
    fill_access_fact(&f4, 0x500, 32, 8, 1);
    CHECK(osprey_table_insert_access(run, &f4) == 1, "mutation fact");
    CHECK(ctx->access_facts->len == 3,
          "mutation observations never committed");
    CHECK(ctx->total_samples == 1, "mutation run commits nothing");

    /* Next baseline: prepare + child facts; commit; mutation fact must
     * not appear and old facts keep one support per sample. */
    osprey_shared_run_prepare(ctx, run, 3);
    CHECK(run->total_facts_count == 2,
          "next prepare discards prior suffix fact count");
    fill_access_fact(&f2, 0x200, 8, 8, 1);
    CHECK(osprey_table_insert_access(run, &f2) == 1, "baseline-2 child");
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK,
          "baseline 2 commit");
    CHECK(ctx->access_facts->len == 3, "baseline 2 adds no new fact");
    CHECK(ctx->total_samples == 2, "two committed samples");
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *cand = &g_array_index(ctx->access_facts,
                                                OspreyAccessFact, i);
        CHECK(cand->pc != 0x500, "mutation fact absent from committed");
    }
    OspreyAccessFact *m2 = NULL;
    for (guint i = 0; i < ctx->access_facts->len; i++) {
        OspreyAccessFact *cand = &g_array_index(ctx->access_facts,
                                                OspreyAccessFact, i);
        if (cand->pc == 0x200) {
            m2 = cand;
        }
    }
    CHECK(m2 != NULL && m2->sample_support == 2,
          "f2 support one per committed sample");

    osprey_free(ctx);
    g_free(run);
}

/* Pre-sample fatal publication: registration-time arithmetic failure
 * marks every reset shared run bad_arithmetic so the baseline merge
 * rejects fail-closed. */
static void test_pre_sample_fatal(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);

    /* Injected overflow: the image-relative end exceeds INT64_MAX. */
    osprey_set_image_bounds(0x400000, 0x401000);
    target_ulong huge = (target_ulong)0x400000 + (target_ulong)INT64_MAX;
    osprey_register_image_global(NULL, huge, 2);
    CHECK(ctx->pre_sample_fatal, "context records pre-sample fatal");

    OspreySharedRun *run = new_run(&c);
    CHECK(run->bad_arithmetic == 1, "reset run carries bad_arithmetic");
    CHECK(osprey_shared_run_freeze_prefix(ctx, run),
          "fatal prefix freezes for deterministic rejection");
    osprey_shared_run_prepare(ctx, run, 1);
    CHECK(run->bad_arithmetic == 1,
          "prepare preserves frozen pre-sample fatal state");
    OspreyStatus st = osprey_parent_merge_sample(ctx, run);
    CHECK(st == OSPREY_INCOMPLETE_FACTS, "pre-sample fatal merge rejects");
    CHECK(strcmp(osprey_tx_stage(ctx), "merge") == 0,
          "pre-sample fatal tx stage");
    CHECK(strcmp(ctx->tx_reason, "global range offset+size overflow") == 0,
          "pre-sample fatal preserves first reason");
    CHECK(ctx->access_facts->len == 0, "pre-sample fatal no partial merge");
    CHECK(g_reject_rows == 1, "pre-sample fatal one reject row");

    osprey_free(ctx);
    g_free(run);
    osprey_clear_pre_sample_fatal();
}


/* ------------------------------------------------------------------ */
/* Stage 2.5: allocator facts, calloc geometry, complete dump contract */
/* ------------------------------------------------------------------ */

static void fill_alloc_fact(OspreyMallocFact *f, uint64_t site,
                            uint64_t size) {
    memset(f, 0, sizeof(*f));
    f->site_pc = site;
    f->requested_size = size;
    f->sample_support = 1;
}

static void fill_mayarray_fact(OspreyMayArrayFact *f, uint8_t kind,
                               uint64_t site, int64_t off,
                               uint64_t count, uint64_t esz,
                               uint32_t evidence) {
    memset(f, 0, sizeof(*f));
    f->start.region.kind = kind;
    f->start.region.code_image_id = 0;
    f->start.region.site_offset = site;
    f->start.offset = off;
    f->element_count = count;
    f->element_size = esz;
    f->evidence_kind = evidence;
    f->sample_support = 1;
}

/* F05 only after a successful allocation; failures, calloc overflow,
 * NULL zero-size returns, out-of-image sites, and stale provenance
 * identities publish nothing. */
static void test_allocator_fact_success_boundary(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    osprey_set_image_bounds(0x400000, 0x401000);
    osprey_child_use_shared_run(ctx, run);
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    provenance_init();

    /* Successful malloc: F05 (site, 24), no F06. */
    PtrTag t = provenance_create_object(0x1000, 24, 0x400200,
                                        PROV_PRODUCER_MALLOC_RETURN);
    OspreyAllocatorObservation obs = {
        .kind = OSPREY_ALLOCATOR_MALLOC,
        .site_pc = 0x400200,
        .requested_size = 24,
    };
    osprey_on_alloc_success(env, &obs, 0x1000, t.object_id, t.generation);
    CHECK(ctx->alloc_facts->len == 0, "facts committed only after merge");

    /* Failed malloc: diagnostic only, no fact, no region. */
    OspreyAllocatorObservation fail = {
        .kind = OSPREY_ALLOCATOR_MALLOC,
        .site_pc = 0x400210,
        .requested_size = 32,
    };
    osprey_on_alloc_failure(&fail);
    OspreyRegionId r;
    int64_t off;
    CHECK(!osprey_region_of_addr(env, 0x9000, &r, &off, false),
          "failed allocation creates no region");

    /* Out-of-image site: ordinary skip. */
    PtrTag t2 = provenance_create_object(0x2000, 48, 0x999999,
                                         PROV_PRODUCER_MALLOC_RETURN);
    OspreyAllocatorObservation out_img = {
        .kind = OSPREY_ALLOCATOR_MALLOC,
        .site_pc = 0x999999,
        .requested_size = 48,
    };
    osprey_on_alloc_success(env, &out_img, 0x2000, t2.object_id,
                            t2.generation);

    /* Successful calloc(3,16): F05 total 48 plus real F06. */
    PtrTag tc = provenance_create_object(0x5000, 48, 0x400240,
                                         PROV_PRODUCER_CALLOC_RETURN);
    OspreyAllocatorObservation calloc_obs = {
        .kind = OSPREY_ALLOCATOR_CALLOC,
        .site_pc = 0x400240,
        .requested_size = 48,
        .element_count = 3,
        .element_size = 16,
    };
    osprey_on_alloc_success(env, &calloc_obs, 0x5000, tc.object_id,
                            tc.generation);

    /* Zero-size malloc success: F05 size 0. */
    PtrTag tz = provenance_create_object(0x6000, 0, 0x400250,
                                         PROV_PRODUCER_MALLOC_RETURN);
    OspreyAllocatorObservation zero = {
        .kind = OSPREY_ALLOCATOR_MALLOC,
        .site_pc = 0x400250,
        .requested_size = 0,
    };
    osprey_on_alloc_success(env, &zero, 0x6000, tz.object_id, tz.generation);

    /* Width boundary: both geometry fields exceed uint32_t while their
     * checked product remains inside the canonical signed-size bound. */
    uint64_t wide_count = (uint64_t)UINT32_MAX + 1;
    uint64_t wide_element_size = 2;
    uint64_t wide_total = wide_count * wide_element_size;
    PtrTag tw = provenance_create_object(0x7000, wide_total, 0x400260,
                                         PROV_PRODUCER_CALLOC_RETURN);
    OspreyAllocatorObservation wide = {
        .kind = OSPREY_ALLOCATOR_CALLOC,
        .site_pc = 0x400260,
        .requested_size = wide_total,
        .element_count = wide_count,
        .element_size = wide_element_size,
    };
    osprey_on_alloc_success(env, &wide, 0x7000, tw.object_id,
                            tw.generation);

    /* Stale provenance identity and malformed allocator kind are
     * sticky transaction failures on their own runs: each rejects its
     * sample fail-closed before any publication. */
    OspreySharedRun *run2 = new_run(&c);
    osprey_child_use_shared_run(ctx, run2);
    OspreyAllocatorObservation stale = {
        .kind = OSPREY_ALLOCATOR_MALLOC,
        .site_pc = 0x400220,
        .requested_size = 64,
    };
    osprey_on_alloc_success(env, &stale, 0x3000, 0xdeadbeef, 999);
    CHECK(run2->bad_identity == 1, "stale identity sticky");
    CHECK(osprey_parent_merge_sample(ctx, run2) == OSPREY_INCOMPLETE_FACTS,
          "stale identity merge rejects");
    CHECK(ctx->alloc_facts->len == 0, "stale identity publishes nothing");

    OspreySharedRun *run3 = new_run(&c);
    osprey_child_use_shared_run(ctx, run3);
    OspreyAllocatorObservation bad_kind = {
        .kind = (OspreyAllocatorKind)77,
        .site_pc = 0x400230,
        .requested_size = 8,
    };
    osprey_on_alloc_success(env, &bad_kind, 0x4000, 1, 1);
    CHECK(run3->bad_identity == 1, "malformed kind sticky");
    CHECK(osprey_parent_merge_sample(ctx, run3) == OSPREY_INCOMPLETE_FACTS,
          "malformed kind merge rejects");

    OspreySharedRun *run4 = new_run(&c);
    osprey_child_use_shared_run(ctx, run4);
    osprey_on_alloc_success(env, NULL, 0x4100, 1, 1);
    CHECK(run4->bad_identity == 1 && run4->alloc_used == 0,
          "NULL success observation rejects before publication");

    OspreySharedRun *run5 = new_run(&c);
    osprey_child_use_shared_run(ctx, run5);
    OspreyAllocatorObservation null_success = {
        .kind = OSPREY_ALLOCATOR_MALLOC,
        .site_pc = 0x400231,
        .requested_size = 0,
    };
    osprey_on_alloc_success(env, &null_success, 0, 1, 1);
    CHECK(run5->bad_identity == 1 && run5->alloc_used == 0,
          "NULL zero-size success event rejects as malformed");

    OspreySharedRun *run6 = new_run(&c);
    osprey_child_use_shared_run(ctx, run6);
    OspreyAllocatorObservation malloc_overflow = {
        .kind = OSPREY_ALLOCATOR_MALLOC,
        .site_pc = 0x400232,
        .requested_size = 8,
        .overflowed = true,
    };
    osprey_on_alloc_success(env, &malloc_overflow, 0x4200, 1, 1);
    CHECK(run6->bad_identity == 1 && run6->bad_arithmetic == 0 &&
          run6->alloc_used == 0,
          "non-calloc overflow flag is malformed identity");

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");
    /* Facts: malloc24 + calloc48 + zero + wide calloc = 4 (no
     * failure, no out-of-image, no stale). */
    CHECK(ctx->alloc_facts->len == 4, "exactly four F05 rows");
    bool saw_24 = false, saw_48 = false, saw_0 = false, saw_wide = false;
    for (guint i = 0; i < ctx->alloc_facts->len; i++) {
        OspreyMallocFact *f = &g_array_index(ctx->alloc_facts,
                                             OspreyMallocFact, i);
        if (f->site_pc == 0x200 && f->requested_size == 24) saw_24 = true;
        if (f->site_pc == 0x240 && f->requested_size == 48) saw_48 = true;
        if (f->site_pc == 0x250 && f->requested_size == 0) saw_0 = true;
        if (f->site_pc == 0x260 && f->requested_size == wide_total) {
            saw_wide = true;
        }
    }
    CHECK(saw_24, "F05 malloc site+24");
    CHECK(saw_48, "F05 calloc site+48");
    CHECK(saw_0, "F05 zero-size success");
    CHECK(saw_wide, "F05 preserves wide calloc total");
    /* F06 only from positive calloc geometries. */
    CHECK(ctx->mayarray_facts->len == 2, "exactly two F06 rows");
    OspreyMayArrayFact *m = NULL;
    OspreyMayArrayFact *wide_m = NULL;
    for (guint i = 0; i < ctx->mayarray_facts->len; i++) {
        OspreyMayArrayFact *candidate = &g_array_index(
            ctx->mayarray_facts, OspreyMayArrayFact, i);
        if (candidate->element_count == 3 &&
            candidate->element_size == 16) m = candidate;
        if (candidate->element_count == wide_count &&
            candidate->element_size == wide_element_size) wide_m = candidate;
    }
    CHECK(m != NULL, "F06 carries exact calloc geometry");
    CHECK(m != NULL && m->evidence_kind == OSPREY_MAY_ARRAY_CALLOC_GEOMETRY,
          "F06 named evidence kind");
    CHECK(m != NULL && m->start.region.kind == OSPREY_REGION_HEAP_SITE &&
          m->start.region.site_offset == 0x240 && m->start.offset == 0,
          "F06 canonical H_site+0 start");
    CHECK(wide_m != NULL && wide_m->element_count == wide_count &&
          wide_m->element_size == wide_element_size,
          "F06 preserves 64-bit geometry");

    osprey_free(ctx);
    g_free(run);
    g_free(run2);
    g_free(run3);
    g_free(run4);
    g_free(run5);
    g_free(run6);
    g_free(env);
    osprey_clear_pre_sample_fatal();
}

/* F06 only from checked positive calloc geometry: exact (3,16) and
 * (1,24), same-total distinct geometries, zero-operand rejection,
 * overflow/product-mismatch rejection, no malloc/realloc F06, 64-bit
 * fields, and matching F05 totals. */
static void test_calloc_geometry_f06(void)
{
    reset_log();
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    osprey_set_image_bounds(0x400000, 0x401000);
    osprey_child_use_shared_run(ctx, run);
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));
    provenance_init();

    /* calloc(3,16) at one site and calloc(1,24) at another. */
    PtrTag c1 = provenance_create_object(0x1000, 48, 0x400200,
                                         PROV_PRODUCER_CALLOC_RETURN);
    OspreyAllocatorObservation o1 = {
        .kind = OSPREY_ALLOCATOR_CALLOC,
        .site_pc = 0x400200,
        .requested_size = 48,
        .element_count = 3,
        .element_size = 16,
    };
    osprey_on_alloc_success(env, &o1, 0x1000, c1.object_id, c1.generation);

    PtrTag c2 = provenance_create_object(0x2000, 24, 0x400210,
                                         PROV_PRODUCER_CALLOC_RETURN);
    OspreyAllocatorObservation o2 = {
        .kind = OSPREY_ALLOCATOR_CALLOC,
        .site_pc = 0x400210,
        .requested_size = 24,
        .element_count = 1,
        .element_size = 24,
    };
    osprey_on_alloc_success(env, &o2, 0x2000, c2.object_id, c2.generation);

    /* Two positive calloc geometries with the same total at one site:
     * one F05 (site,total), two distinct F06 rows. */
    PtrTag c3 = provenance_create_object(0x3000, 48, 0x400200,
                                         PROV_PRODUCER_CALLOC_RETURN);
    OspreyAllocatorObservation o3 = {
        .kind = OSPREY_ALLOCATOR_CALLOC,
        .site_pc = 0x400200,
        .requested_size = 48,
        .element_count = 2,
        .element_size = 24,
    };
    osprey_on_alloc_success(env, &o3, 0x3000, c3.object_id, c3.generation);

    /* Matching malloc/realloc totals remain F05-only even when they
     * could be factored into the same geometry. */
    PtrTag m = provenance_create_object(0x3500, 48, 0x400218,
                                         PROV_PRODUCER_MALLOC_RETURN);
    OspreyAllocatorObservation mo = {
        .kind = OSPREY_ALLOCATOR_MALLOC,
        .site_pc = 0x400218,
        .requested_size = 48,
    };
    osprey_on_alloc_success(env, &mo, 0x3500, m.object_id, m.generation);
    PtrTag rr = provenance_create_object(0x3600, 48, 0x400219,
                                         PROV_PRODUCER_REALLOC_RETURN);
    OspreyAllocatorObservation rro = {
        .kind = OSPREY_ALLOCATOR_REALLOC,
        .site_pc = 0x400219,
        .requested_size = 48,
    };
    osprey_on_alloc_success(env, &rro, 0x3600, rr.object_id, rr.generation);

    /* Zero count and zero element size: F05 only. */
    PtrTag z1 = provenance_create_object(0x4000, 0, 0x400220,
                                         PROV_PRODUCER_CALLOC_RETURN);
    OspreyAllocatorObservation z1o = {
        .kind = OSPREY_ALLOCATOR_CALLOC,
        .site_pc = 0x400220,
        .requested_size = 0,
        .element_count = 0,
        .element_size = 16,
    };
    osprey_on_alloc_success(env, &z1o, 0x4000, z1.object_id, z1.generation);

    PtrTag z2 = provenance_create_object(0x5000, 0, 0x400230,
                                         PROV_PRODUCER_CALLOC_RETURN);
    OspreyAllocatorObservation z2o = {
        .kind = OSPREY_ALLOCATOR_CALLOC,
        .site_pc = 0x400230,
        .requested_size = 0,
        .element_count = 4,
        .element_size = 0,
    };
    osprey_on_alloc_success(env, &z2o, 0x5000, z2.object_id, z2.generation);

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK,
          "geometry baseline merge");
    CHECK(ctx->alloc_facts->len == 6,
          "malloc/realloc and calloc F05 totals");
    CHECK(ctx->mayarray_facts->len == 3,
          "only positive calloc observations emit F06");

    /* Product mismatch: inconsistent internal event, sticky failure. */
    OspreySharedRun *run2 = new_run(&c);
    osprey_child_use_shared_run(ctx, run2);
    provenance_init();
    PtrTag pm = provenance_create_object(0x6000, 48, 0x400240,
                                         PROV_PRODUCER_CALLOC_RETURN);
    OspreyAllocatorObservation pmo = {
        .kind = OSPREY_ALLOCATOR_CALLOC,
        .site_pc = 0x400240,
        .requested_size = 48,
        .element_count = 5,
        .element_size = 16,
    };
    osprey_on_alloc_success(env, &pmo, 0x6000, pm.object_id, pm.generation);
    CHECK(run2->bad_identity == 1 && run2->bad_arithmetic == 0,
          "product mismatch is an identity failure");
    CHECK(run2->alloc_used == 0, "product mismatch publishes no F05");
    CHECK(run2->mayarray_used == 0, "product mismatch publishes no F06");
    CHECK(osprey_parent_merge_sample(ctx, run2) == OSPREY_INCOMPLETE_FACTS,
          "product mismatch merge rejects");
    CHECK(ctx->alloc_facts->len == 6 && ctx->mayarray_facts->len == 3,
          "product mismatch committed nothing");

    /* Product overflow is arithmetic-invalid before provenance lookup or
     * any table publication. */
    OspreySharedRun *run3 = new_run(&c);
    osprey_child_use_shared_run(ctx, run3);
    OspreyAllocatorObservation overflow = {
        .kind = OSPREY_ALLOCATOR_CALLOC,
        .site_pc = 0x400241,
        .requested_size = 0,
        .element_count = UINT64_MAX,
        .element_size = 2,
        .overflowed = true,
    };
    osprey_on_alloc_success(env, &overflow, 0, 0, 0);
    CHECK(run3->bad_arithmetic == 1, "calloc overflow arithmetic sticky");
    CHECK(run3->alloc_used == 0 && run3->mayarray_used == 0,
          "calloc overflow publishes no facts");
    CHECK(osprey_parent_merge_sample(ctx, run3) == OSPREY_INCOMPLETE_FACTS,
          "calloc overflow merge rejects");

    /* The signed canonical-size bound and base-end arithmetic are both
     * fail-closed even when the provenance object is otherwise valid. */
    OspreySharedRun *run4 = new_run(&c);
    osprey_child_use_shared_run(ctx, run4);
    uint64_t too_large = (uint64_t)INT64_MAX + 1;
    PtrTag large = provenance_create_object(0x8000, too_large, 0x400242,
                                            PROV_PRODUCER_MALLOC_RETURN);
    OspreyAllocatorObservation large_obs = {
        .kind = OSPREY_ALLOCATOR_MALLOC,
        .site_pc = 0x400242,
        .requested_size = too_large,
    };
    osprey_on_alloc_success(env, &large_obs, 0x8000,
                            large.object_id, large.generation);
    CHECK(run4->bad_arithmetic == 1 && run4->alloc_used == 0,
          "oversized allocation rejects before publication");
    CHECK(osprey_parent_merge_sample(ctx, run4) == OSPREY_INCOMPLETE_FACTS,
          "oversized allocation merge rejects");

    OspreySharedRun *run5 = new_run(&c);
    osprey_child_use_shared_run(ctx, run5);
    PtrTag end = provenance_create_object(UINT64_MAX - 7, 16, 0x400243,
                                          PROV_PRODUCER_MALLOC_RETURN);
    OspreyAllocatorObservation end_obs = {
        .kind = OSPREY_ALLOCATOR_MALLOC,
        .site_pc = 0x400243,
        .requested_size = 16,
    };
    osprey_on_alloc_success(env, &end_obs, UINT64_MAX - 7,
                            end.object_id, end.generation);
    CHECK(run5->bad_arithmetic == 1 && run5->alloc_used == 0,
          "base-end overflow rejects before publication");
    CHECK(osprey_parent_merge_sample(ctx, run5) == OSPREY_INCOMPLETE_FACTS,
          "base-end overflow merge rejects");
    CHECK(ctx->alloc_facts->len == 6 && ctx->mayarray_facts->len == 3,
          "arithmetic failures preserve committed baseline");

    osprey_free(ctx);
    g_free(run);
    g_free(run2);
    g_free(run3);
    g_free(run4);
    g_free(run5);
    g_free(env);
    osprey_clear_pre_sample_fatal();
}

/* Transport: alloc/may-array keys, duplicates, prefix/suffix union,
 * cross-sample support, saturation, version pin, failed diagnostics
 * consume no rows, and may-array table exhaustion rejects at merge. */
static void test_allocator_transport_support_and_limits(void)
{
    reset_log();
    CHECK(OSPREY_SHARED_VERSION == 10u, "shared format version 10");
    CHECK(sizeof(OspreyMallocFact) == 24 && _Alignof(OspreyMallocFact) == 8,
          "version-10 F05 fixed layout");
    CHECK(sizeof(OspreyMayArrayFact) == 56 &&
              _Alignof(OspreyMayArrayFact) == 8,
          "version-10 F06 fixed layout");

    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);

    /* Duplicate insertion in either order merges in place; support
     * stays Boolean inside one sample. */
    OspreyMallocFact a1, a2;
    fill_alloc_fact(&a1, 0x300, 48);
    fill_alloc_fact(&a2, 0x310, 24);
    CHECK(osprey_table_insert_alloc(run, &a1) == 1, "insert alloc 1");
    CHECK(osprey_table_insert_alloc(run, &a2) == 1, "insert alloc 2");
    CHECK(osprey_table_insert_alloc(run, &a1) == 0,
          "alloc duplicate merges in place");
    CHECK(run->alloc_used == 2, "two unique alloc records");
    OspreyMayArrayFact m1, m2;
    fill_mayarray_fact(&m1, OSPREY_REGION_HEAP_SITE, 0x300, 0, 3, 16, 0);
    fill_mayarray_fact(&m2, OSPREY_REGION_HEAP_SITE, 0x310, 0, 1, 24, 0);
    CHECK(osprey_table_insert_mayarray(run, &m1) == 1, "insert may 1");
    CHECK(osprey_table_insert_mayarray(run, &m2) == 1, "insert may 2");
    CHECK(osprey_table_insert_mayarray(run, &m1) == 0,
          "may duplicate merges in place");
    CHECK(run->mayarray_used == 2, "two unique may records");

    /* Prefix/suffix union: same alloc fact in both parts contributes
     * one Boolean support; a distinct child fact adds one row. */
    CHECK(osprey_shared_run_freeze_prefix(ctx, run), "freeze");
    osprey_shared_run_prepare(ctx, run, 1);
    CHECK(osprey_table_insert_alloc(run, &a1) == 1,
          "prefix alloc duplicate copied into child");
    CHECK(osprey_table_insert_mayarray(run, &m1) == 1,
          "prefix may-array duplicate copied into child");
    CHECK(run->total_facts_count == 4,
          "prefix duplicates keep union count");
    OspreyMallocFact a3;
    fill_alloc_fact(&a3, 0x320, 96);
    CHECK(osprey_table_insert_alloc(run, &a3) == 1, "child-only alloc");
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");
    CHECK(ctx->alloc_facts->len == 3, "union of three alloc facts");
    CHECK(ctx->mayarray_facts->len == 2,
          "union of two may-array facts");
    for (guint i = 0; i < ctx->mayarray_facts->len; i++) {
        OspreyMayArrayFact *f = &g_array_index(ctx->mayarray_facts,
                                               OspreyMayArrayFact, i);
        CHECK(f->sample_support == 1,
              "may-array support is Boolean within one sample");
    }
    for (guint i = 0; i < ctx->alloc_facts->len; i++) {
        OspreyMallocFact *f = &g_array_index(ctx->alloc_facts,
                                             OspreyMallocFact, i);
        CHECK(f->sample_support == 1, "Boolean support per sample");
        CHECK(f->requested_size <= INT64_MAX, "unsigned 64-bit size");
    }
    /* A later committed sample increments support exactly once. */
    osprey_shared_run_prepare(ctx, run, 2);
    CHECK(osprey_table_insert_alloc(run, &a1) == 1,
          "second-sample alloc duplicate copied into child");
    CHECK(osprey_table_insert_mayarray(run, &m1) == 1,
          "second-sample may-array duplicate copied into child");
    CHECK(run->total_facts_count == 4,
          "second-sample duplicates keep prefix union count");
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK,
          "second baseline merge");
    OspreyMallocFact *fa = NULL;
    OspreyMayArrayFact *fm = NULL;
    for (guint i = 0; i < ctx->alloc_facts->len; i++) {
        OspreyMallocFact *f = &g_array_index(ctx->alloc_facts,
                                             OspreyMallocFact, i);
        if (f->site_pc == 0x300 && f->requested_size == 48) fa = f;
    }
    for (guint i = 0; i < ctx->mayarray_facts->len; i++) {
        OspreyMayArrayFact *f = &g_array_index(ctx->mayarray_facts,
                                               OspreyMayArrayFact, i);
        if (osprey_mayarray_eq(f, &m1)) fm = f;
    }
    CHECK(fa != NULL && fa->sample_support == 2,
          "F05 support increments once per committed sample");
    CHECK(fm != NULL && fm->sample_support == 2,
          "F06 support increments once per committed sample");

    /* Parent-side support accumulation saturates for both families. */
    if (fa != NULL) fa->sample_support = UINT32_MAX;
    if (fm != NULL) fm->sample_support = UINT32_MAX;
    osprey_shared_run_prepare(ctx, run, 3);
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK,
          "saturation sample merges");
    CHECK(fa != NULL && fa->sample_support == UINT32_MAX,
          "F05 support saturates at UINT32_MAX");
    CHECK(fm != NULL && fm->sample_support == UINT32_MAX,
          "F06 support saturates at UINT32_MAX");

    /* Failed diagnostics consume no shared rows: run3 stays empty. */
    OspreySharedRun *run3 = new_run(&c);
    osprey_child_use_shared_run(ctx, run3);
    OspreyAllocatorObservation fail = {
        .kind = OSPREY_ALLOCATOR_MALLOC,
        .site_pc = 0x400400,
        .requested_size = 16,
    };
    osprey_set_image_bounds(0x400000, 0x401000);
    osprey_on_alloc_failure(&fail);
    CHECK(run3->alloc_used == 0 && run3->mayarray_used == 0,
          "failed diagnostic consumes no shared rows");
    CHECK(run3->total_facts_count == 0, "failed diagnostic no fact count");

    /* Independent fixed-table exhaustion: each allocator family must
     * fail closed without borrowing capacity from another family. */
    OspreySharedRun *alloc_full = new_run(&c);
    alloc_full->alloc_cap = 1;
    OspreyMallocFact cap_a, cap_b;
    fill_alloc_fact(&cap_a, 0x340, 8);
    fill_alloc_fact(&cap_b, 0x350, 8);
    CHECK(osprey_table_insert_alloc(alloc_full, &cap_a) == 1,
          "allocator table first row");
    CHECK(osprey_table_insert_alloc(alloc_full, &cap_b) < 0 &&
          alloc_full->overflow == 1,
          "allocator table exhaustion is sticky");

    OspreySharedRun *may_full = new_run(&c);
    may_full->mayarray_cap = 1;
    OspreyMayArrayFact cap_m1, cap_m2;
    fill_mayarray_fact(&cap_m1, OSPREY_REGION_HEAP_SITE, 0x340, 0,
                       1, 8, OSPREY_MAY_ARRAY_CALLOC_GEOMETRY);
    fill_mayarray_fact(&cap_m2, OSPREY_REGION_HEAP_SITE, 0x350, 0,
                       1, 8, OSPREY_MAY_ARRAY_CALLOC_GEOMETRY);
    CHECK(osprey_table_insert_mayarray(may_full, &cap_m1) == 1,
          "may-array table first row");
    CHECK(osprey_table_insert_mayarray(may_full, &cap_m2) < 0 &&
          may_full->overflow == 1,
          "may-array table exhaustion is sticky");

    guint committed_allocs = ctx->alloc_facts->len;
    guint committed_mays = ctx->mayarray_facts->len;
    CHECK(osprey_parent_merge_sample(ctx, alloc_full) ==
              OSPREY_INCOMPLETE_FACTS,
          "allocator table exhaustion rejects at merge");
    CHECK(ctx->alloc_facts->len == committed_allocs,
          "allocator exhaustion commits no partial row");

    /* F05 may be inserted before truthful F06 hits its independent
     * table cap.  The sticky overflow must reject both atomically. */
    OspreySharedRun *partial = new_run(&c);
    partial->mayarray_cap = 1;
    CHECK(osprey_table_insert_alloc(partial, &cap_a) == 1,
          "partial sample inserts F05 first");
    CHECK(osprey_table_insert_mayarray(partial, &cap_m1) == 1,
          "partial sample inserts first F06");
    CHECK(osprey_table_insert_mayarray(partial, &cap_m2) < 0 &&
          partial->overflow == 1,
          "second F06 exhausts partial sample");
    CHECK(osprey_parent_merge_sample(ctx, partial) ==
              OSPREY_INCOMPLETE_FACTS,
          "partial F05/F06 sample rejects at merge");
    CHECK(ctx->alloc_facts->len == committed_allocs &&
          ctx->mayarray_facts->len == committed_mays,
          "partial allocator sample commits neither family");

    /* The total-fact cap is independent of either table capacity. */
    OspreySharedRun *fact_full = new_run(&c);
    fact_full->max_facts_cfg = 1;
    CHECK(osprey_table_insert_alloc(fact_full, &cap_a) == 1,
          "total-fact cap first row");
    CHECK(osprey_table_insert_alloc(fact_full, &cap_b) < 0 &&
          fact_full->overflow == 1,
          "total-fact cap exhaustion is sticky");

    OspreySharedRun *bad_may = new_run(&c);
    OspreyMayArrayFact malformed_may = cap_m1;
    malformed_may.sample_support = 2;
    CHECK(osprey_table_insert_mayarray(bad_may, &malformed_may) == 1,
          "malformed may-array support inserted for validation");
    CHECK(osprey_parent_merge_sample(ctx, bad_may) ==
              OSPREY_INCOMPLETE_FACTS,
          "malformed may-array support rejected");
    CHECK(ctx->mayarray_facts->len == 2,
          "malformed may-array support commits nothing");

    OspreySharedRun *bad_alloc = new_run(&c);
    OspreyMallocFact oversized;
    fill_alloc_fact(&oversized, 0x360, (uint64_t)INT64_MAX + 1);
    CHECK(osprey_table_insert_alloc(bad_alloc, &oversized) == 1,
          "oversized transported F05 inserted for validation");
    CHECK(osprey_parent_merge_sample(ctx, bad_alloc) ==
              OSPREY_INCOMPLETE_FACTS,
          "oversized transported F05 rejects before rules");

    OspreySharedRun *bad_geometry = new_run(&c);
    OspreyMallocFact geometry_total;
    OspreyMayArrayFact bad_start;
    fill_alloc_fact(&geometry_total, 0x370, 48);
    fill_mayarray_fact(&bad_start, OSPREY_REGION_HEAP_SITE, 0x370, -8,
                       3, 16, OSPREY_MAY_ARRAY_CALLOC_GEOMETRY);
    CHECK(osprey_table_insert_alloc(bad_geometry, &geometry_total) == 1,
          "matching F05 inserted for malformed F06");
    CHECK(osprey_table_insert_mayarray(bad_geometry, &bad_start) == 1,
          "malformed F06 start inserted for validation");
    CHECK(osprey_parent_merge_sample(ctx, bad_geometry) ==
              OSPREY_INCOMPLETE_FACTS,
          "noncanonical F06 start rejects before rules");

    OspreySharedRun *missing_total = new_run(&c);
    OspreyMayArrayFact orphan = cap_m1;
    orphan.start.region.site_offset = 0x380;
    CHECK(osprey_table_insert_mayarray(missing_total, &orphan) == 1,
          "orphan F06 inserted for validation");
    CHECK(osprey_parent_merge_sample(ctx, missing_total) ==
              OSPREY_INCOMPLETE_FACTS,
          "F06 without matching F05 rejects before rules");
    CHECK(ctx->alloc_facts->len == committed_allocs &&
          ctx->mayarray_facts->len == committed_mays,
          "malformed allocator transport commits nothing");

    OspreyConfig tiny = c;
    tiny.shared_bytes = 1;
    OspreyContext *tiny_ctx = osprey_new(&tiny);
    OspreySharedRun *byte_run = new_run(&c);
    CHECK(osprey_parent_merge_sample(tiny_ctx, byte_run) ==
              OSPREY_INCOMPLETE_FACTS,
          "shared-byte layout exhaustion rejects");
    CHECK(tiny_ctx->alloc_facts->len == 0,
          "shared-byte rejection commits nothing");
    osprey_free(tiny_ctx);
    g_free(byte_run);

    g_free(alloc_full);
    g_free(may_full);
    g_free(partial);
    g_free(fact_full);
    g_free(bad_may);
    g_free(bad_alloc);
    g_free(bad_geometry);
    g_free(missing_total);
    g_free(run3);
    osprey_free(ctx);
    g_free(run);
    osprey_clear_pre_sample_fatal();
}

/* Complete F01-F06 dump contract: exact schemas, all-field order,
 * canonical F06 starts, 64-bit values, support fields, uniqueness, no raw
 * addresses, and no negative alloc rows.  Signed copy/points dump order is
 * pinned separately by test_copy_points_merge_and_dump(). */
static void test_complete_f01_f06_dump_contract(void)
{
    reset_log();
    OspreyConfig c = test_config();
    snprintf(c.dump_file, sizeof(c.dump_file), "/tmp/osprey_f06_dump.txt");
    unlink(c.dump_file);
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);

    /* Deliberately shuffled rows from every family. */
    OspreyAccessFact f;
    memset(&f, 0, sizeof(f));
    f.pc = 0x500;
    f.chunk.address.region.kind = OSPREY_REGION_GLOBAL;
    f.chunk.address.offset = 0x8000;
    f.chunk.size = 8;
    f.dynamic_count = 1;
    f.sample_support = 1;
    CHECK(osprey_table_insert_access(run, &f) == 1, "insert access");

    OspreyBaseFact b;
    memset(&b, 0, sizeof(b));
    b.pc = 0x510;
    b.chunk.address.region.kind = OSPREY_REGION_GLOBAL;
    b.chunk.address.offset = 0x8000;
    b.chunk.size = 8;
    b.base.region.kind = OSPREY_REGION_GLOBAL;
    b.base.offset = 0x8000;
    b.producer_pc = 0x60;
    b.sample_support = 1;
    CHECK(osprey_table_insert_base(run, &b) == 1, "insert base");

    OspreyCopyFact cp;
    memset(&cp, 0, sizeof(cp));
    cp.source.address.region.kind = OSPREY_REGION_GLOBAL;
    cp.source.address.offset = 0x8000;
    cp.source.size = 8;
    cp.destination.address.region.kind = OSPREY_REGION_GLOBAL;
    cp.destination.address.offset = 0x8010;
    cp.destination.size = 8;
    cp.sample_support = 1;
    CHECK(osprey_table_insert_copy(run, &cp) == 1, "insert copy");

    OspreyPointsToFact pt;
    memset(&pt, 0, sizeof(pt));
    pt.pointer_chunk.address.region.kind = OSPREY_REGION_GLOBAL;
    pt.pointer_chunk.address.offset = 0x8020;
    pt.pointer_chunk.size = 8;
    pt.target.region.kind = OSPREY_REGION_HEAP_SITE;
    pt.target.region.site_offset = 0x300;
    pt.target.offset = 0;
    pt.sample_support = 1;
    CHECK(osprey_table_insert_points(run, &pt) == 1, "insert points");

    OspreyMallocFact a1, a2;
    fill_alloc_fact(&a1, 0x310, 24);
    fill_alloc_fact(&a2, 0x300, 32);
    CHECK(osprey_table_insert_alloc(run, &a1) == 1, "insert alloc shuffled");
    CHECK(osprey_table_insert_alloc(run, &a2) == 1, "insert alloc 2");
    /* Same-site distinct sizes stay distinct facts. */
    OspreyMallocFact a3;
    fill_alloc_fact(&a3, 0x300, 48);
    CHECK(osprey_table_insert_alloc(run, &a3) == 1, "same site new size");

    /* Positive calloc geometries keep the canonical H_site+0 start;
     * two distinct pairs may carry the same total. */
    OspreyMayArrayFact m1, m2, m3;
    fill_mayarray_fact(&m1, OSPREY_REGION_HEAP_SITE, 0x310, 0, 1, 24, 0);
    fill_mayarray_fact(&m2, OSPREY_REGION_HEAP_SITE, 0x300, 0, 2, 24, 0);
    fill_mayarray_fact(&m3, OSPREY_REGION_HEAP_SITE, 0x300, 0, 3, 16, 0);
    CHECK(osprey_table_insert_mayarray(run, &m1) == 1, "insert may 1");
    CHECK(osprey_table_insert_mayarray(run, &m2) == 1, "insert may 2");
    CHECK(osprey_table_insert_mayarray(run, &m3) == 1,
          "insert same-total may-array geometry");

    /* Valid success size 0 row. */
    OspreyMallocFact z;
    fill_alloc_fact(&z, 0x320, 0);
    CHECK(osprey_table_insert_alloc(run, &z) == 1, "zero-size success");

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");
    FILE *fp = fopen(c.dump_file, "r");
    CHECK(fp != NULL, "dump written");
    char lines[64][256];
    int n = 0;
    if (fp != NULL) {
        char line[256];
        while (fgets(line, sizeof(line), fp) && n < 64) {
            size_t len = strlen(line);
            if (len > 0 && line[len - 1] == '\n') line[len - 1] = '\0';
            snprintf(lines[n], sizeof(lines[n]), "%s", line);
            CHECK(strstr(lines[n], "0x") == NULL,
                  "canonical dump has no raw address prefix");
            n++;
        }
        fclose(fp);
    }
    /* Find family boundaries. */
    int alloc_start = -1, may_start = -1;
    for (int i = 0; i < n; i++) {
        if (strncmp(lines[i], "alloc ", 6) == 0 && alloc_start < 0)
            alloc_start = i;
        if (strncmp(lines[i], "may-array ", 9) == 0 && may_start < 0)
            may_start = i;
    }
    CHECK(alloc_start >= 0, "alloc rows present");
    CHECK(may_start >= 0, "may-array rows present");
    /* Alloc rows sorted by (site, size, support); no negative rows. */
    int allocs = 0;
    uint64_t prev_site = 0, prev_size = 0;
    bool first_alloc = true;
    for (int i = alloc_start; i < n; i++) {
        if (strncmp(lines[i], "alloc ", 6) != 0) break;
        uint64_t site, size; unsigned sup;
        CHECK(sscanf(lines[i], "alloc %llx %llu %u",
                     (unsigned long long *)&site,
                     (unsigned long long *)&size, &sup) == 3,
              "alloc schema: site size support");
        CHECK(!strstr(lines[i], "-1"), "no negative alloc row");
        if (!first_alloc) {
            CHECK(site > prev_site ||
                  (site == prev_site && size >= prev_size),
                  "alloc sorted by site then size");
        }
        first_alloc = false;
        prev_site = site;
        prev_size = size;
        allocs++;
    }
    CHECK(allocs == 4, "four alloc rows");
    /* May-array rows sorted in schema order with canonical zero starts
     * and exact 64-bit geometry. */
    int mays = 0;
    for (int i = may_start; i < n; i++) {
        if (strncmp(lines[i], "may-array ", 9) != 0) break;
        unsigned kind, ev, sup;
        unsigned long long site, off, cnt, esz;
        CHECK(sscanf(lines[i],
                     "may-array %u %llx %llx %llu %llu %u %u",
                     &kind, &site, &off, &cnt, &esz, &ev, &sup) == 7,
              "may-array schema: kind site offset count size evidence "
              "support");
        CHECK(cnt > 0 && esz > 0, "positive calloc geometry only");
        mays++;
    }
    CHECK(mays == 3, "three may-array rows");
    /* Order: geometry (2,24) before (3,16) at site 0x300, then
     * the site-0x310 row.  Every real F06 start is H_site+0. */
    CHECK(strstr(lines[may_start],
                 "may-array 1 300 0 2 24 0 1") == lines[may_start],
          "may-array first row exact");
    CHECK(strstr(lines[may_start + 1],
                 "may-array 1 300 0 3 16 0 1") == lines[may_start + 1],
          "may-array second row has canonical zero start");
    CHECK(strstr(lines[may_start + 2],
                 "may-array 1 310 0 1 24 0 1") == lines[may_start + 2],
          "may-array third row exact");

    unlink(c.dump_file);
    osprey_free(ctx);
    g_free(run);
    osprey_clear_pre_sample_fatal();
}

/* ------------------------------------------------------------------ */

int main(void)
{
    test_overflow_rejection();
    test_bad_arithmetic_rejection();
    test_bad_identity_rejection();
    test_version_mismatch_rejection();
    test_capacity_mismatch_rejection();
    test_used_exceeds_cap_rejection();
    test_population_mismatch_rejection();
    test_unsupported_execution_rejection();
    test_happy_merge_analyze_and_hide();
    test_recovery_after_rejection();
    test_variable_cap_rejection();
    test_factor_cap_rejection();
    test_empty_graph_rejection();
    test_exact_component_cap_rejection();
    test_decoder_cap_rejection();
    test_key_collision_fixtures();
    test_factor_key_bidirectional();
    test_pc_normalization_and_global_merge();
    test_heap_identity_lifecycle();
    test_realloc_lifecycle_variants();
    test_stack_frames_and_rsp_origin();
    test_entrypoint_frame_seeding();
    test_stack_resync();
    test_observed_stack_bounds();
    test_prefix_suffix_composition();
    test_child_only_sample();
    test_duplicate_dynamic_observation();
    test_counter_saturation();
    test_fact_cap_rejection();
    test_chunk_cap_rejection();
    test_mutation_run_isolated();
    test_pre_sample_fatal();
    test_allocator_fact_success_boundary();
    test_calloc_geometry_f06();
    test_allocator_transport_support_and_limits();
    test_complete_f01_f06_dump_contract();
    test_canonical_dump();
    test_sem_manifest_integrity();
    test_sem_overwrite_fail_closed();
    test_sem_access_class_and_flags();
    test_address_origin_channels_and_producers();
    test_address_shadow_reload();
    test_f02_ea_selection();
    test_base_fact_producer_merge();
    test_value_origin_creation_and_transfer();
    test_ordinary_f03_f04_publication();
    test_osprey_shadow_overlap_invalidation();
    test_modeled_copy_origins_and_facts();
    test_copy_points_merge_and_dump();

    if (failures != 0) {
        fprintf(stderr, "%d unit test check(s) FAILED\n", failures);
        return 1;
    }
    printf("PASS osprey_unit (50/50)\n");
    return 0;
}

/* ------------------------------------------------------------------ */
/* Semantic-event manifest (Stage 2.2)                                 */
/* ------------------------------------------------------------------ */

static void test_sem_manifest_integrity(void)
{
    /* Every class has a name; every name is non-empty. */
    for (int i = 0; i < SEM_OP_CLASS_COUNT; i++) {
        CHECK(sem_op_class_name[i] != NULL, "class name present");
        CHECK(sem_op_class_name[i][0] != '\0', "class name non-empty");
    }
    /* Only UNKNOWN is invalid (fail-closed fallback). */
    CHECK(!sem_op_class_valid[SEM_OP_UNKNOWN], "UNKNOWN invalid");
    int valid_count = 0;
    for (int i = 0; i < SEM_OP_CLASS_COUNT; i++) {
        if (sem_op_class_valid[i]) valid_count++;
    }
    CHECK(valid_count == SEM_OP_CLASS_COUNT - 1, "exactly one invalid");

    /* The classified and emittable helper sets must be an exact,
     * duplicate-free match. */
    int n_helpers = 0;
    for (const SemHelperClass *h = sem_helper_class_table;
         h->helper_name != NULL; h++, n_helpers++) {
        CHECK(h->helper_name[0] != '\0', "helper name non-empty");
        CHECK((unsigned int)h->op_class < SEM_OP_CLASS_COUNT,
              "helper class in range");
        CHECK(sem_op_class_valid[(unsigned int)h->op_class],
              "helper class valid");
        int matches = 0;
        for (const char *const *e = sem_emittable_helpers; *e != NULL; e++) {
            if (strcmp(*e, h->helper_name) == 0) {
                matches++;
            }
        }
        CHECK(matches == 1, "classified helper appears once in emit set");
    }
    CHECK(n_helpers != 0, "semantic helper set is non-empty");

    int n_emittable = 0;
    for (const char *const *e = sem_emittable_helpers; *e != NULL; e++) {
        int matches = 0;
        for (const SemHelperClass *h = sem_helper_class_table;
             h->helper_name != NULL; h++) {
            if (strcmp(*e, h->helper_name) == 0) {
                matches++;
            }
        }
        CHECK(matches == 1, "emittable helper appears once in class set");
        n_emittable++;
    }
    CHECK(n_emittable == n_helpers, "semantic helper sets have equal size");

    CHECK(SEM_PRODUCER_COUNT <=
              (SEM_MEM_PRODUCER_MASK >> SEM_MEM_PRODUCER_SHIFT) + 1,
          "producer IDs fit packed event flags");
    CHECK(SEM_INTERVAL_UNSUPPORTED <=
              (SEM_MEM_POLICY_MASK >> SEM_MEM_POLICY_SHIFT),
          "interval policies fit packed event flags");
    int n_producers = 0;
    bool seen_class[SEM_OP_CLASS_COUNT] = { false };
    for (const SemProducerSpec *p = sem_producer_table;
         p->producer != NULL; p++, n_producers++) {
        CHECK((unsigned int)n_producers < SEM_PRODUCER_COUNT &&
              (SemProducerId)n_producers != SEM_PRODUCER_INVALID,
              "producer row has a representable family ID");
        CHECK((unsigned int)n_producers ==
                  (unsigned int)(p - sem_producer_table),
              "producer row ID follows manifest order");
        CHECK(p->producer[0] != '\0', "producer name non-empty");
        int name_matches = 0;
        for (const SemProducerSpec *q = sem_producer_table;
             q->producer != NULL; q++) {
            if (strcmp(p->producer, q->producer) == 0) {
                name_matches++;
            }
        }
        CHECK(name_matches == 1, "producer name appears once");
        CHECK((unsigned int)p->op_class < SEM_OP_CLASS_COUNT,
              "producer class in range");
        CHECK(sem_op_class_valid[(unsigned int)p->op_class],
              "producer class valid");
        CHECK(p->interval_policy <= SEM_INTERVAL_UNSUPPORTED,
              "producer interval policy valid");
        CHECK(p->coverage != NULL && p->coverage[0] != '\0',
              "producer coverage description present");
        CHECK(p->supported ==
              (p->interval_policy != SEM_INTERVAL_UNSUPPORTED),
              "producer support agrees with interval policy");
        if (p->interval_policy == SEM_INTERVAL_DYNAMIC) {
            CHECK(p->supported, "dynamic producer is supported");
            CHECK(p->interval_widths == NULL &&
                  p->interval_width_count == 0,
                  "dynamic producer has no invented fixed widths");
        } else if (p->supported) {
            CHECK(p->interval_widths != NULL &&
                  p->interval_width_count != 0,
                  "supported producer advertises interval widths");
            for (uint32_t i = 0; i < p->interval_width_count; i++) {
                CHECK(p->interval_widths[i] != 0,
                      "producer interval width is nonzero");
                if (i != 0) {
                    CHECK(p->interval_widths[i - 1] < p->interval_widths[i],
                          "producer interval widths are strictly sorted");
                }
            }
        } else {
            CHECK(p->interval_widths == NULL && p->interval_width_count == 0,
                  "unsupported producer has no interval widths");
            CHECK(p->coverage != NULL && p->coverage[0] != '\0',
                  "unsupported producer has concrete reason");
        }
        seen_class[(unsigned int)p->op_class] = true;
    }
    CHECK(n_producers == SEM_PRODUCER_COUNT,
          "manifest rows have one family ID each");
    for (int i = 0; i < SEM_OP_UNKNOWN; i++) {
        CHECK(seen_class[i], "producer matrix covers operation class");
    }
}

static void test_sem_overwrite_fail_closed(void)
{
    CPUArchState env;
    PtrTag tag;
    memset(&env, 0, sizeof(env));
    memset(&tag, 0, sizeof(tag));
    tag.valid = true;
    tag.concrete_value = 0x1000;

    OspreyCpuOriginState *ost = osprey_cpu_origin(&env);
    ost->regs[R_EAX].address.valid = 1;
    ost->regs[R_EAX].address.width = sizeof(target_ulong);
    provenance_set_reg_tag(&env, R_EAX, tag);
    provenance_mem_store_tag(0x1000, tag);

    /* Inactive consumers retain their private state. */
    binradar_memcheck_enabled = 0;
    osprey_collect_enabled = 0;
    sem_reg_overwrite(&env, R_EAX, SEM_OP_SNAPSHOT);
    sem_mem_overwrite(&env, 0x1000, 8, SEM_OP_SNAPSHOT);
    CHECK(provenance_get_reg_tag(&env, R_EAX).valid,
          "inactive provenance register unchanged");
    CHECK(provenance_mem_load_tag(0x1000).valid,
          "inactive provenance memory unchanged");
    CHECK(ost->regs[R_EAX].address.valid,
          "inactive OSPREY register unchanged");

    /* Invalid class values are bounds-safe and still fail closed for an
     * active consumer by invalidating, never by preserving metadata. */
    binradar_memcheck_enabled = 1;
    sem_reg_overwrite(&env, R_EAX, (SemOpClass)SEM_OP_CLASS_COUNT);
    sem_mem_overwrite(&env, 0x1000, 8, (SemOpClass)-1);
    CHECK(!provenance_get_reg_tag(&env, R_EAX).valid,
          "invalid class kills provenance register");
    CHECK(!provenance_mem_load_tag(0x1000).valid,
          "negative class kills provenance memory");

    /* OSPREY register/context overwrites kill origins and consume any
     * fault-left EA record without requiring provenance to be active. */
    binradar_memcheck_enabled = 0;
    osprey_collect_enabled = 1;
    ost->regs[R_EAX].address.valid = 1;
    ost->regs[R_EAX].address.width = sizeof(target_ulong);
    ost->regs[R_EAX].address.concrete_value = 0;
    helper_sem_on_store(&env, R_EAX, 0x402000, 8, 0,
                        SEM_OP_INTEGER);
    ost->regs[R_EBX].address.valid = 0;
    helper_sem_on_store(&env, R_EAX, 0x402000, 8, 0,
                        (uint32_t)-1);
    helper_sem_on_load(&env, R_EBX, 0x402000, 8, 0x400100,
                       SEM_OP_INTEGER);
    CHECK(!ost->regs[R_EBX].address.valid,
          "invalid class clears OSPREY memory shadow");
    ost->regs[R_EAX].address.valid = 1;
    ost->regs[R_EAX].address.width = sizeof(target_ulong);
    sem_reg_overwrite(&env, R_EAX, SEM_OP_UNKNOWN);
    CHECK(!ost->regs[R_EAX].address.valid,
          "OSPREY register overwrite invalidates");

    for (int i = 0; i < CPU_NB_REGS; i++) {
        ost->regs[i].address.valid = 1;
        ost->regs[i].address.width = sizeof(target_ulong);
    }
    ost->ea.valid = true;
    ost->ea_mode = MO_64;
    ost->ea.base_origin.valid = 1;
    ost->ea.index_origin.valid = 1;
    sem_context_replace(&env);
    for (int i = 0; i < CPU_NB_REGS; i++) {
        CHECK(!ost->regs[i].address.valid,
              "context replacement kills OSPREY reg");
    }
    CHECK(!ost->ea.valid && ost->ea_mode == 0,
          "context replacement consumes EA metadata");
    CHECK(!ost->ea.base_origin.valid && !ost->ea.index_origin.valid,
          "context replacement clears EA origins");

    ost->regs[R_EAX].address.valid = 1;
    ost->regs[R_EBX].address.valid = 1;
    sem_clobber_caller_saved(&env);
    CHECK(!ost->regs[R_EAX].address.valid,
          "modeled call kills caller-saved origin");
    CHECK(ost->regs[R_EBX].address.valid,
          "modeled call keeps callee-saved origin");

    sem_reg_overwrite(NULL, 0, SEM_OP_UNKNOWN);
    sem_context_replace(NULL);
    osprey_collect_enabled = 0;
}

static void test_sem_access_class_and_flags(void)
{
    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);
    CPUArchState *env = g_malloc0(sizeof(CPUArchState));

    osprey_set_image_bounds(0x400000, 0x401000);
    osprey_register_image_global(NULL, 0x402000, 0x1000);
    osprey_child_use_shared_run(ctx, run);
    binradar_memcheck_enabled = 0;
    osprey_collect_enabled = 1;

    /* A valid SIMD class on a plain F01 event records exactly one access. */
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x402008, 8, 0x400100, 8, SEM_OP_SIMD,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_SIMD_SCALAR);
    CHECK(run->access_used == 1, "valid class records F01 access");
    CHECK(!st->ea.valid && st->ea_mode == 0,
          "plain event consumes EA state");

    /* Operation class is part of F01 identity: the same PC/address/width
     * under two classes yields two rows, while an exact duplicate merges. */
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x402008, 8, 0x400100, 8, SEM_OP_ATOMIC_RMW,
                   SEM_INTERVAL_EXACT_WIDTH,
                   SEM_PRODUCER_ATOMIC_LOCK_RMW);
    CHECK(run->access_used == 2, "different classes remain distinct facts");
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x402008, 8, 0x400100, 8, SEM_OP_ATOMIC_RMW,
                   SEM_INTERVAL_EXACT_WIDTH,
                   SEM_PRODUCER_ATOMIC_LOCK_RMW);
    CHECK(run->access_used == 2, "same class fact merges exactly");

    /* Probe every fixed manifest row through the actual runtime dispatcher.
     * Unique PCs keep rows independent; a valid width/policy pair must
     * publish, while dynamic rows are intentionally covered by their
     * class-carrying overwrite API. */
    uint32_t policy_probe = 0;
    uint32_t expected_accesses = run->access_used;
    for (const SemProducerSpec *p = sem_producer_table;
         p->producer != NULL; p++) {
        if (!p->supported || p->interval_policy == SEM_INTERVAL_DYNAMIC) {
            continue;
        }
        for (uint32_t i = 0; i < p->interval_width_count; i++) {
            st->ea_mode = MO_64;
            sem_mem_access(env, 0x402100 + policy_probe,
                           p->interval_widths[i],
                           0x400200 + policy_probe, 8, p->op_class,
                           p->interval_policy,
                           (SemProducerId)(p - sem_producer_table));
            expected_accesses++;
            policy_probe++;
        }
    }
    CHECK(run->access_used == expected_accesses &&
          run->unsupported_execution == 0,
          "every fixed manifest policy/width pair publishes");
    /* Keep the following rejection/cardinality assertions focused on their
     * original two-row fixture rather than coupling them to probe volume. */
    osprey_shared_run_reset(run, 1, &c);
    osprey_child_use_shared_run(ctx, run);
    fill_two_access_facts(run);
    st->ea.valid = false;
    st->ea_mode = 0;
    st->pending_helper_count = 0;

    /* A class/policy pair absent from the manifest rejects the sample rather
     * than publishing a fact under a class-unioned width contract. */
    run->unsupported_execution = 0;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x40200c, 8, 0x400104, 8, SEM_OP_INTEGER,
                   SEM_INTERVAL_RAW, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->access_used == 2,
          "undeclared policy suppresses F01 access");
    CHECK(run->unsupported_execution == 1,
          "undeclared policy rejects the sample");
    CHECK(!st->ea.valid && st->ea_mode == 0,
          "undeclared policy clears EA state");
    osprey_collect_enabled = 1;

    run->unsupported_execution = 0;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x40200c, 8, 0x400104, 8, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INVALID);
    CHECK(run->access_used == 2 && run->unsupported_execution == 1,
          "invalid producer family rejects F01 access");
    CHECK(!st->ea.valid && st->ea_mode == 0,
          "invalid producer family clears EA state");
    osprey_collect_enabled = 1;

    run->unsupported_execution = 0;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x40200c, 24, 0x400108, 8, SEM_OP_PAIRED,
                   SEM_INTERVAL_SPARSE, SEM_PRODUCER_XSAVE_FXSAVE);
    CHECK(run->access_used == 2 && run->unsupported_execution == 1,
          "cross-family width rejects F01 access");
    CHECK(!st->ea.valid && st->ea_mode == 0,
          "cross-family width clears EA state");
    osprey_collect_enabled = 1;

    run->unsupported_execution = 0;
    st->ea_mode = MO_64;
    sem_mem_maskmov(env, 0x40200c, 1, 32, 0x40010c, SEM_OP_SIMD,
                    SEM_INTERVAL_SPARSE, SEM_PRODUCER_SIMD_MASKMOV);
    CHECK(run->access_used == 2 && run->unsupported_execution == 1,
          "invalid sparse width rejects F01 access");
    CHECK(!st->ea.valid && st->ea_mode == 0,
          "invalid sparse width clears EA state");
    osprey_collect_enabled = 1;

    /* Unknown classes reject the sample without recording, and still consume
     * the state left by a preceding failed/unsupported path. */
    run->unsupported_execution = 0;
    st->ea.valid = true;
    st->ea_mode = MO_64;
    st->ea.base_reg = R_EAX;
    st->ea.base_val = 0x402010;
    st->ea.base_origin.valid = 1;
    st->pending_helper_count = 1;
    sem_mem_access(env, 0x402010, 8, 0x400100, 8,
                   (SemOpClass)-1, SEM_INTERVAL_EXACT_WIDTH,
                   SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->access_used == 2, "invalid class suppresses F01 access");
    CHECK(!st->ea.valid && st->ea_mode == 0,
          "invalid class clears EA state");
    CHECK(st->ea.base_reg == 0 && st->ea.base_val == 0 &&
          !st->ea.base_origin.valid,
          "invalid class clears all EA metadata");
    CHECK(st->pending_helper_count == 0,
          "invalid class clears multipart state");
    CHECK(run->unsupported_execution == 1,
          "invalid class rejects incomplete F01 sample");
    osprey_collect_enabled = 1;

    /* Bit 4 is the provenance-only follow-up for an EA-decomposed
     * operation; it must not create a duplicate F01 row. */
    st->ea.valid = true;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x402018, 8, 0x400100, 4, SEM_OP_ATOMIC_RMW,
                   SEM_INTERVAL_EXACT_WIDTH,
                   SEM_PRODUCER_ATOMIC_LOCK_RMW);
    CHECK(run->access_used == 2, "EA follow-up suppresses duplicate F01");
    CHECK(!st->ea.valid && st->ea_mode == 0,
          "EA follow-up clears pending state");

    st->ea.valid = true;
    st->ea_mode = MO_64;
    st->ea.index_reg = R_ECX;
    st->ea.index_val = 0x402020;
    st->ea.index_origin.valid = 1;
    sem_mem_access(env, 0x402020, 8, 0x400100, 4, SEM_OP_SIMD,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_SIMD_SCALAR);
    CHECK(st->ea.index_reg == 0 && st->ea.index_val == 0 &&
          !st->ea.index_origin.valid,
          "provenance-only follow-up clears all EA metadata");

    st->ea.valid = true;
    st->ea_mode = MO_32;
    st->ea.base_origin.valid = 1;
    sem_mem_access(env, 0x402028, 8, 0x400100, 8, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->access_used == 2, "ineligible address mode suppresses F01");
    CHECK(!st->ea.valid && st->ea_mode == 0 &&
          !st->ea.base_origin.valid,
          "ineligible address mode clears EA state");

    /* Helper-backed events retain provenance dispatch when OSPREY is off. */
    binradar_memcheck_enabled = 1;
    osprey_collect_enabled = 0;
    PtrRegShadow *prov = provenance_get_reg_shadow(env);
    memset(&prov->ea_meta, 0, sizeof(prov->ea_meta));
    prov->ea_meta.valid = true;
    prov->ea_meta.aflags = MO_32;
    sem_mem_helper_access(env, 0x402030, 8, 0x400110, false,
                          SEM_OP_INTEGER, SEM_INTERVAL_EXACT_WIDTH,
                          SEM_PRODUCER_INTEGER_MODRM);
    CHECK(!prov->ea_meta.valid,
          "provenance-only helper event consumes EA metadata");

    osprey_collect_enabled = 1;
    run->unsupported_execution = 0;
    st->ea_mode = MO_64;
    sem_mem_helper_access(env, 0x402038, 8, 0x400118, false,
                          SEM_OP_MPX, SEM_INTERVAL_EXACT_WIDTH,
                          SEM_PRODUCER_MPX_BNDX_HELPER);
    CHECK(run->access_used == 2,
          "helper undeclared policy suppresses F01 access");
    CHECK(run->unsupported_execution == 1,
          "helper undeclared policy rejects the sample");

    /* Multipart helpers buffer every constituent until the final
     * post-success callback.  A first successful part must not publish a
     * partial F01 fact set that would survive a later fault. */
    binradar_memcheck_enabled = 0;
    osprey_collect_enabled = 1;
    st->ea_mode = MO_64;
    sem_mem_helper_access_part(env, 0x402040, 8, 0x400120, false,
                               SEM_OP_MPX, SEM_INTERVAL_MULTIPART,
                               SEM_PRODUCER_MPX_BNDX_HELPER, false);
    CHECK(run->access_used == 2,
          "multipart first part remains unpublished");
    sem_mem_helper_access_part(env, 0x402080, 24, 0x400120, false,
                               SEM_OP_MPX, SEM_INTERVAL_MULTIPART,
                               SEM_PRODUCER_MPX_BNDX_HELPER, true);
    CHECK(run->access_used == 4,
          "multipart final part publishes all intervals");

    run->unsupported_execution = 0;
    st->ea_mode = MO_64;
    sem_mem_helper_access_part(env, 0x4020a0, 4, 0x400124, true,
                               SEM_OP_PAIRED, SEM_INTERVAL_SPARSE,
                               SEM_PRODUCER_XSAVE_FXSAVE, false);
    sem_mem_helper_access_part(env, 0x4020a8, 4, 0x400124, true,
                               SEM_OP_PAIRED, SEM_INTERVAL_SPARSE,
                               SEM_PRODUCER_XSAVE_XSAVE, false);
    CHECK(st->pending_helper_count == 0 && run->unsupported_execution == 1,
          "mixed multipart producer rows reject the aggregate");
    osprey_collect_enabled = 1;

    /* Exceeding the fixed multipart buffer must reject the sample, not
     * silently discard a known-incomplete helper footprint. */
    run->unsupported_execution = 0;
    st->ea_mode = MO_64;
    for (uint32_t i = 0; i < OSPREY_MAX_PENDING_HELPER_INTERVALS; i++) {
        sem_mem_helper_access_part(env, 0x402100 + i, 1, 0x400128,
                                   true, SEM_OP_SIMD, SEM_INTERVAL_SPARSE,
                                   SEM_PRODUCER_SIMD_MASKMOV, false);
    }
    CHECK(st->pending_helper_count == OSPREY_MAX_PENDING_HELPER_INTERVALS,
          "multipart buffer accepts its exact bounded capacity");
    sem_mem_helper_access_part(env, 0x402200, 1, 0x400128, true,
                               SEM_OP_SIMD, SEM_INTERVAL_SPARSE,
                               SEM_PRODUCER_SIMD_MASKMOV, false);
    CHECK(st->pending_helper_count == 0 && st->ea_mode == 0,
          "multipart overflow clears buffered semantic state");
    CHECK(run->unsupported_execution == 1,
          "multipart overflow rejects incomplete sample");
    CHECK(run->access_used == 4,
          "multipart overflow publishes no partial F01 rows");

    run->unsupported_execution = 0;
    osprey_collect_enabled = 1;
    st->ea_mode = MO_64;
    st->ea.valid = true;
    st->pending_helper_count = 1;
    helper_sem_mem_unsupported(env, 0x400130, 1);
    CHECK(st->pending_helper_count == 0 && !st->ea.valid &&
          st->ea_mode == 0,
          "unsupported helper clears pending semantic state");
    CHECK(run->unsupported_execution == 1,
          "unsupported helper rejects incomplete sample");

    binradar_memcheck_enabled = 0;
    osprey_collect_enabled = 0;
    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

/* ------------------------------------------------------------------ */
/* Stage 2.3: address-origin channels and ordinary producer identity   */
/* ------------------------------------------------------------------ */

/* A shared env+context fixture for the Stage 2.3 tests.  Image bounds
 * [0x400000, 0x401000); global data at 0x402000 (offset 0x2000). */
static void stage23_setup(OspreyConfig *c, OspreyContext **ctx,
                          OspreySharedRun **run, CPUArchState **env) {
    *c = test_config();
    *ctx = osprey_new(c);
    *run = new_run(c);
    osprey_set_image_bounds(0x400000, 0x401000);
    osprey_register_image_global(NULL, 0x402000, 0x1000);
    osprey_child_use_shared_run(*ctx, *run);
    *env = g_malloc0(sizeof(CPUArchState));
    binradar_memcheck_enabled = 0;
    osprey_collect_enabled = 1;
}

static void install_addr_origin(OspreyCpuOriginState *st, int reg,
                                target_ulong value,
                                const OspreyRegionId *region,
                                int64_t offset, uint64_t producer_pc) {
    OspreyAddressOrigin *o = &st->regs[reg].address;
    memset(o, 0, sizeof(*o));
    o->valid = 1;
    o->width = (uint8_t)sizeof(target_ulong);
    o->concrete_value = value;
    o->canonical.region = *region;
    o->canonical.offset = offset;
    o->producer_pc = producer_pc;
}

static void test_address_origin_channels_and_producers(void)
{
    reset_log();
    OspreyConfig c;
    OspreyContext *ctx;
    OspreySharedRun *run;
    CPUArchState *env;
    stage23_setup(&c, &ctx, &run, &env);
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    OspreyRegionId G, S, H;
    memset(&G, 0, sizeof(G));
    G.kind = OSPREY_REGION_GLOBAL;
    memset(&S, 0, sizeof(S));
    S.kind = OSPREY_REGION_STACK_FUNCTION;
    S.site_offset = 0x500;
    memset(&H, 0, sizeof(H));
    H.kind = OSPREY_REGION_HEAP_SITE;
    H.site_offset = 0x300;
    (void)run;

    /* Global materialization: a RIP-relative/absolute main-image
     * address seeds a G origin with the normalized instruction PC. */
    osprey_on_reg_materialize_address(env, R_R8, 0x402008, 0x400600);
    CHECK(st->regs[R_R8].address.valid &&
          st->regs[R_R8].address.width == sizeof(target_ulong),
          "global materialization seeds valid pointer-width origin");
    CHECK(st->regs[R_R8].address.canonical.region.kind ==
              OSPREY_REGION_GLOBAL &&
          st->regs[R_R8].address.canonical.offset == 0x2008,
          "global materialization canonical G+0x2008");
    CHECK(st->regs[R_R8].address.producer_pc == 0x600,
          "global materialization producer PC normalized");
    CHECK(st->regs[R_R8].address.concrete_value == 0x402008,
          "global materialization concrete value");
    CHECK(!st->regs[R_R8].value.valid, "materialization clears value channel");

    /* Out-of-image / non-global values never seed: libc address,
     * anonymous map, or a merely mapped numeric value. */
    osprey_on_reg_materialize_address(env, R_R9, 0x7f0000001234, 0x400610);
    CHECK(!st->regs[R_R9].address.valid, "libc materialization rejected");
    osprey_on_reg_materialize_address(env, R_R10, 0x402000, 0x7f0012345678);
    CHECK(!st->regs[R_R10].address.valid,
          "out-of-image producer PC kills destination");

    /* Precise stack seed: RSP origin with normalized callee entry as
     * producer. */
    osprey_on_call(env, 0x400500, 0x7ffc0000);
    CHECK(st->regs[R_ESP].address.valid &&
          st->regs[R_ESP].address.canonical.region.site_offset == 0x500 &&
          st->regs[R_ESP].address.canonical.offset == 0,
          "precise callee seeds RSP at frame offset 0");
    CHECK(st->regs[R_ESP].address.producer_pc == 0x500,
          "stack seed producer PC is the normalized callee entry");
    osprey_on_rsp_update(env, 0x7ffbfff0, 0x400501);
    CHECK(st->regs[R_ESP].address.canonical.offset == -16,
          "rsp update re-derives signed offset");
    CHECK(st->regs[R_ESP].address.producer_pc == 0x501,
          "rsp update producer PC is the write instruction");
    /* A malformed source origin cannot replace the independently
     * re-derived RSP lifecycle seed. */
    install_addr_origin(st, R_R8, 0x7ffbfff0, &H, 0, 0x300);
    osprey_on_reg_copy(env, R_ESP, R_R8, 0x7ffbfff0, 0x7ffbfff0,
                       0x400502);
    CHECK(st->regs[R_ESP].address.valid &&
          st->regs[R_ESP].address.canonical.region.kind ==
              OSPREY_REGION_STACK_FUNCTION &&
          st->regs[R_ESP].address.canonical.offset == -16 &&
          st->regs[R_ESP].address.producer_pc == 0x501,
          "invalid MOV-to-RSP source preserves lifecycle seed");
    osprey_on_rsp_update(env, 0x7ffbffe0, 0x400503);
    osprey_on_reg_addsub_imm(env, R_ESP, -16, 0x7ffbfff0,
                             0x7ffbffe0, 0x400503);
    CHECK(st->regs[R_ESP].address.valid &&
          st->regs[R_ESP].address.canonical.offset == -32 &&
          st->regs[R_ESP].address.producer_pc == 0x503,
          "post-write RSP lifecycle seed survives ADD/SUB helper ordering");

    /* Allocator return: RAX gets H_site+0 with provenance identity. */
    provenance_init();
    PtrTag t = provenance_create_object(0x10000, 64, 0x400300,
                                        PROV_PRODUCER_MALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_MALLOC,
            .site_pc = 0x400300,
            .requested_size = 64,
        };
        osprey_on_alloc_success(env, &obs, 0x10000, t.object_id, t.generation);
    }
    CHECK(st->regs[R_EAX].address.valid &&
          st->regs[R_EAX].address.canonical.region.kind ==
              OSPREY_REGION_HEAP_SITE &&
          st->regs[R_EAX].address.canonical.offset == 0,
          "allocator return seeds RAX H_site+0");
    CHECK(st->regs[R_EAX].address.prov_object_id == t.object_id &&
          st->regs[R_EAX].address.prov_generation == t.generation,
          "allocator origin carries provenance identity");
    CHECK(st->regs[R_EAX].address.producer_pc == 0x300,
          "allocator origin producer PC is the normalized site");
    install_addr_origin(st, R_R8, 0x10040, &H, 64, 0x300);
    st->regs[R_R8].address.prov_object_id = t.object_id;
    st->regs[R_R8].address.prov_generation = t.generation;
    CHECK(osprey_address_origin_live(&st->regs[R_R8].address),
          "live heap origin permits the architectural one-past address");

    /* Full-width MOV: copies the channel, replaces producer PC. */
    install_addr_origin(st, R_R12, 0x402010, &G, 0x2010, 0x700);
    st->regs[R_R13].value.valid = 1;
    osprey_on_reg_copy(env, R_R13, R_R12, 0x402010, 0x402010, 0x400710);
    CHECK(st->regs[R_R13].address.valid &&
          st->regs[R_R13].address.canonical.offset == 0x2010 &&
          st->regs[R_R13].address.producer_pc == 0x710,
          "full-width MOV copies channel and replaces producer PC");
    CHECK(!st->regs[R_R13].value.valid, "MOV clears destination value channel");
    osprey_on_reg_copy(env, R_R12, R_R12, 0x402010, 0x402010, 0x400715);
    CHECK(st->regs[R_R12].address.valid &&
          st->regs[R_R12].address.canonical.offset == 0x2010 &&
          st->regs[R_R12].address.producer_pc == 0x715,
          "self-MOV preserves the source origin and refreshes producer PC");
    osprey_on_reg_copy(env, R_R13, R_R12, 0xdeadbeef, 0x402010, 0x400720);
    CHECK(!st->regs[R_R13].address.valid,
          "value-mismatched MOV kills destination");
    osprey_on_reg_copy(env, R_R13, R_R12, 0x402010, 0x402010, 0x7f0012345678);
    CHECK(!st->regs[R_R13].address.valid,
          "out-of-image MOV producer kills destination");

    /* Constant-offset LEA: exact wrapping reconstruction + checked
     * offset fold; producer PC becomes the LEA instruction. */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    osprey_on_reg_lea(env, R_R13, R_R12, 8, 0x10008, 0x10000, 0x400800);
    CHECK(st->regs[R_R13].address.valid &&
          st->regs[R_R13].address.canonical.offset == 8 &&
          st->regs[R_R13].address.producer_pc == 0x800,
          "constant LEA folds offset and sets LEA producer");
    CHECK(st->regs[R_R13].address.prov_object_id == t.object_id,
          "LEA preserves heap provenance identity");
    osprey_on_reg_lea(env, R_R12, R_R12, 4, 0x10004, 0x10000, 0x400805);
    CHECK(st->regs[R_R12].address.valid &&
          st->regs[R_R12].address.canonical.offset == 4 &&
          st->regs[R_R12].address.producer_pc == 0x805,
          "in-place LEA preserves the pre-write base origin");
    /* Restore H+0 for the reconstruction-mismatch case. */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    osprey_on_reg_lea(env, R_R13, R_R12, 8, 0x10009, 0x10000, 0x400810);
    CHECK(!st->regs[R_R13].address.valid,
          "reconstruction-mismatched LEA kills destination");
    /* Missing or context-cleared two-helper PC scratch cannot reuse a
     * prior producer identity. */
    helper_sem_reg_lea(env, R_R13, R_R12, 8, 0x10008, 0x10000);
    CHECK(!st->regs[R_R13].address.valid,
          "LEA without producer-PC scratch kills destination");
    helper_sem_set_pc(env, 0x400800);
    sem_context_replace(env);
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    helper_sem_reg_lea(env, R_R13, R_R12, 8, 0x10008, 0x10000);
    CHECK(!st->regs[R_R13].address.valid,
          "context boundary clears stranded LEA producer PC");
    /* Checked offset overflow (INT64_MAX + 1). */
    install_addr_origin(st, R_R12, 0x10000, &H, INT64_MAX, 0x300);
    osprey_on_reg_lea(env, R_R13, R_R12, 1, 0x10001, 0x10000, 0x400820);
    CHECK(!st->regs[R_R13].address.valid,
          "canonical offset overflow kills LEA destination");

    /* ADD/SUB immediate: exact wrapping reconstruction + checked fold. */
    install_addr_origin(st, R_R13, 0x10008, &H, 8, 0x800);
    st->regs[R_R13].address.prov_object_id = t.object_id;
    st->regs[R_R13].address.prov_generation = t.generation;
    osprey_on_reg_addsub_imm(env, R_R13, 4, 0x10008, 0x1000c, 0x400900);
    CHECK(st->regs[R_R13].address.valid &&
          st->regs[R_R13].address.canonical.offset == 12 &&
          st->regs[R_R13].address.producer_pc == 0x900,
          "ADD immediate folds offset and sets producer");
    osprey_on_reg_addsub_imm(env, R_R13, -2, 0x1000c, 0x1000a, 0x400910);
    CHECK(st->regs[R_R13].address.canonical.offset == 10,
          "SUB immediate folds negative delta");
    osprey_on_reg_addsub_imm(env, R_R13, 4, 0x1000c, 0x1000a, 0x400920);
    CHECK(!st->regs[R_R13].address.valid,
          "reconstruction-mismatched ADD immediate kills");
    install_addr_origin(st, R_R13, 0x10000, &H, INT64_MAX, 0x300);
    osprey_on_reg_addsub_imm(env, R_R13, 1, 0x10000, 0x10001, 0x400930);
    CHECK(!st->regs[R_R13].address.valid,
          "canonical offset overflow kills ADD immediate");

    /* ADD/SUB register, one-origin forms. */
    install_addr_origin(st, R_R13, 0x1000a, &H, 10, 0x910);
    st->regs[R_R13].address.prov_object_id = t.object_id;
    st->regs[R_R13].address.prov_generation = t.generation;
    memset(&st->regs[R_R14], 0, sizeof(st->regs[R_R14]));
    env->regs[R_R14] = 1;
    osprey_on_reg_addsub_reg(env, R_R13, R_R14, false, 0x1000b, 1,
                             0x400a00);
    CHECK(st->regs[R_R13].address.valid &&
          st->regs[R_R13].address.canonical.offset == 11 &&
          st->regs[R_R13].address.producer_pc == 0xa00,
          "tagged-destination ADD register folds untagged source");
    /* Untagged destination + tagged source for ADD. */
    install_addr_origin(st, R_R14, 0x10000, &H, 0, 0x300);
    st->regs[R_R14].address.prov_object_id = t.object_id;
    st->regs[R_R14].address.prov_generation = t.generation;
    memset(&st->regs[R_R15], 0, sizeof(st->regs[R_R15]));
    osprey_on_reg_addsub_reg(env, R_R15, R_R14, false, 0x1000c, 0x10000,
                             0x400a10);
    CHECK(st->regs[R_R15].address.valid &&
          st->regs[R_R15].address.canonical.offset == 12 &&
          st->regs[R_R15].address.producer_pc == 0xa10,
          "untagged-destination ADD with tagged source folds");
    /* SUB with only the source tagged is rejected. */
    memset(&st->regs[R_R15], 0, sizeof(st->regs[R_R15]));
    osprey_on_reg_addsub_reg(env, R_R15, R_R14, true, 0xfff0, 0x10000,
                             0x400a20);
    CHECK(!st->regs[R_R15].address.valid,
          "SUB with only source tagged rejected");
    /* Two tagged operands are rejected. */
    install_addr_origin(st, R_R14, 0x10000, &H, 0, 0x300);
    install_addr_origin(st, R_R15, 0x10000, &H, 0, 0x300);
    osprey_on_reg_addsub_reg(env, R_R15, R_R14, false, 0x20000, 0x10000,
                             0x400a30);
    CHECK(!st->regs[R_R15].address.valid,
          "two tagged operands rejected");
    /* Reconstruction mismatch kills. */
    install_addr_origin(st, R_R13, 0x1000a, &H, 10, 0x910);
    memset(&st->regs[R_R14], 0, sizeof(st->regs[R_R14]));
    osprey_on_reg_addsub_reg(env, R_R13, R_R14, false, 0x1000c, 1,
                             0x400a40);
    CHECK(!st->regs[R_R13].address.valid,
          "reconstruction-mismatched ADD register kills");

    /* Full-width XCHG: channels swap with per-side validation; producer
     * PC becomes the XCHG instruction. */
    install_addr_origin(st, R_R13, 0x1000b, &H, 11, 0xa00);
    st->regs[R_R13].address.prov_object_id = t.object_id;
    st->regs[R_R13].address.prov_generation = t.generation;
    memset(&st->regs[R_R15], 0, sizeof(st->regs[R_R15]));
    env->regs[R_R13] = 0x1000b;
    env->regs[R_R15] = 0;
    osprey_on_reg_xchg(env, R_R13, R_R15, 0, 0x1000b, 0x400b00);
    CHECK(!st->regs[R_R13].address.valid &&
          st->regs[R_R15].address.valid &&
          st->regs[R_R15].address.canonical.offset == 11 &&
          st->regs[R_R15].address.producer_pc == 0xb00 &&
          st->regs[R_R15].address.concrete_value == 0x1000b,
          "XCHG transfers tagged channel to untagged side");
    CHECK(st->regs[R_R15].address.prov_object_id == t.object_id,
          "XCHG preserves heap provenance identity");
    /* dst == src validates and refreshes once. */
    install_addr_origin(st, R_R13, 0x10000, &H, 0, 0x300);
    st->regs[R_R13].address.prov_object_id = t.object_id;
    st->regs[R_R13].address.prov_generation = t.generation;
    osprey_on_reg_xchg(env, R_R13, R_R13, 0x10000, 0x10000, 0x400b10);
    CHECK(st->regs[R_R13].address.valid &&
          st->regs[R_R13].address.producer_pc == 0xb10,
          "self-XCHG validates and refreshes the single channel");

    /* RSP-to-RBP: ordinary register-copy propagation. */
    osprey_on_call(env, 0x400500, 0x7ffc0000);
    osprey_on_reg_copy(env, R_EBP, R_ESP, 0x7ffc0000, 0x7ffc0000, 0x400c00);
    CHECK(st->regs[R_EBP].address.valid &&
          st->regs[R_EBP].address.canonical.region.site_offset == 0x500 &&
          st->regs[R_EBP].address.canonical.offset == 0,
          "RSP-to-RBP copy propagates stack origin");
    CHECK(st->regs[R_EBP].address.producer_pc == 0xc00,
          "RSP-to-RBP copy producer PC is the MOV");

    /* Value-channel kills: every register write clears the value
     * channel explicitly. */
    st->regs[R_EAX].value.valid = 1;
    osprey_on_reg_invalidate(env, R_EAX);
    CHECK(!st->regs[R_EAX].address.valid && !st->regs[R_EAX].value.valid,
          "invalidate kills both channels");
    st->regs[R_R8].value.valid = 1;
    osprey_on_reg_materialize_address(env, R_R8, 0x402010, 0x400600);
    CHECK(!st->regs[R_R8].value.valid,
          "materialize clears the value channel");

    /* Invalid register indices are bounds-safe. */
    osprey_on_reg_materialize_address(env, CPU_NB_REGS + 5, 0x402000,
                                      0x400600);
    osprey_on_reg_copy(env, CPU_NB_REGS + 5, R_R8, 0, 0, 0x400600);
    osprey_on_reg_xchg(env, CPU_NB_REGS + 5, R_R8, 0, 0, 0x400600);
    osprey_on_reg_invalidate(env, CPU_NB_REGS + 5);
    install_addr_origin(st, R_R8, 0x402000, &G, 0x2000, 0x600);
    osprey_on_reg_copy(env, R_R8, CPU_NB_REGS + 5, 0, 0, 0x400600);
    CHECK(!st->regs[R_R8].address.valid,
          "invalid MOV source index safely kills destination");
    install_addr_origin(st, R_R8, 0x402000, &G, 0x2000, 0x600);
    osprey_on_reg_lea(env, R_R8, CPU_NB_REGS + 5, 1,
                      0x402001, 0x402000, 0x400600);
    CHECK(!st->regs[R_R8].address.valid,
          "invalid LEA base index safely kills destination");
    install_addr_origin(st, R_R8, 0x402000, &G, 0x2000, 0x600);
    osprey_on_reg_addsub_reg(env, R_R8, CPU_NB_REGS + 5, false,
                             0x402001, 1, 0x400600);
    CHECK(!st->regs[R_R8].address.valid,
          "invalid arithmetic source index safely kills destination");
    install_addr_origin(st, R_R8, 0x10000, &H, 0, 0x300);
    CHECK(!osprey_address_origin_live(&st->regs[R_R8].address),
          "heap origin without provenance identity is invalid");

    provenance_retire_object(0x10000);
    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

static void test_address_shadow_reload(void)
{
    reset_log();
    OspreyConfig c;
    OspreyContext *ctx;
    OspreySharedRun *run;
    CPUArchState *env;
    stage23_setup(&c, &ctx, &run, &env);
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    OspreyRegionId G, H;
    memset(&G, 0, sizeof(G));
    G.kind = OSPREY_REGION_GLOBAL;
    memset(&H, 0, sizeof(H));
    H.kind = OSPREY_REGION_HEAP_SITE;
    H.site_offset = 0x300;

    provenance_init();
    PtrTag t = provenance_create_object(0x10000, 64, 0x400300,
                                        PROV_PRODUCER_MALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_MALLOC,
            .site_pc = 0x400300,
            .requested_size = 64,
        };
        osprey_on_alloc_success(env, &obs, 0x10000, t.object_id, t.generation);
    }

    /* Uninterrupted aligned pointer-width store + reload: the reload
     * restores the origin and sets producer PC to the load. */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402100, 8, 0x10000, 0x400d00);
    memset(&st->regs[R_R13], 0, sizeof(st->regs[R_R13]));
    env->regs[R_R13] = 0x10000;
    osprey_on_mem_load(env, R_R13, 0x402100, 8, 0x400d00);
    CHECK(st->regs[R_R13].address.valid &&
          st->regs[R_R13].address.canonical.offset == 0 &&
          st->regs[R_R13].address.prov_object_id == t.object_id &&
          st->regs[R_R13].address.producer_pc == 0xd00,
          "aligned reload restores origin with load producer PC");
    CHECK(st->regs[R_R13].address.concrete_value == 0x10000,
          "reload concrete value matches runtime");

    /* Exact-slot value mismatch removes the slot and leaves the
     * destination invalid. */
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402110, 8, 0x10000, 0x400d00);
    memset(&st->regs[R_R13], 0, sizeof(st->regs[R_R13]));
    env->regs[R_R13] = 0xdeadbeef;
    osprey_on_mem_load(env, R_R13, 0x402110, 8, 0x400d10);
    CHECK(!st->regs[R_R13].address.valid,
          "value-mismatched reload leaves destination invalid");
    memset(&st->regs[R_R13], 0, sizeof(st->regs[R_R13]));
    env->regs[R_R13] = 0x10000;
    osprey_on_mem_load(env, R_R13, 0x402110, 8, 0x400d20);
    CHECK(!st->regs[R_R13].address.valid,
          "stale slot removed; second reload cannot resurrect");

    /* Stale heap identity: free the object, the reload rejects and
     * removes the slot. */
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402120, 8, 0x10000, 0x400d00);
    osprey_on_free_identity(env, t.object_id, t.generation, 0x400400);
    provenance_retire_object(0x10000);
    memset(&st->regs[R_R13], 0, sizeof(st->regs[R_R13]));
    env->regs[R_R13] = 0x10000;
    osprey_on_mem_load(env, R_R13, 0x402120, 8, 0x400d30);
    CHECK(!st->regs[R_R13].address.valid,
          "stale heap identity rejects reload");

    /* Aligned unknown-source store replaces the exact slot with an
     * invalid entry. */
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402130, 8, 0x10000, 0x400d00);
    memset(&st->regs[R_R12], 0, sizeof(st->regs[R_R12]));
    env->regs[R_R12] = 0x1234;
    osprey_on_mem_store(env, R_R12, 0x402130, 8, 0x10000, 0x400d00);
    memset(&st->regs[R_R13], 0, sizeof(st->regs[R_R13]));
    env->regs[R_R13] = 0x1234;
    osprey_on_mem_load(env, R_R13, 0x402130, 8, 0x400d40);
    CHECK(!st->regs[R_R13].address.valid,
          "unknown-source store replaces slot with invalid entry");

    /* Partial and unaligned stores into previously empty slots do not
     * install an origin (no cross-width invalidation is asserted). */
    install_addr_origin(st, R_R12, 0x402000, &G, 0x2000, 0x600);
    env->regs[R_R12] = 0x402000;
    osprey_on_mem_store(env, R_R12, 0x402200, 4, 0x402000, 0x400d00);
    memset(&st->regs[R_R13], 0, sizeof(st->regs[R_R13]));
    env->regs[R_R13] = 0x402000;
    osprey_on_mem_load(env, R_R13, 0x402200, 8, 0x400d50);
    CHECK(!st->regs[R_R13].address.valid,
          "partial store invalidates and does not install an origin");
    env->regs[R_R12] = 0x402000;
    osprey_on_mem_store(env, R_R12, 0x402204, 8, 0x402000, 0x400d00);
    memset(&st->regs[R_R13], 0, sizeof(st->regs[R_R13]));
    env->regs[R_R13] = 0x402000;
    osprey_on_mem_load(env, R_R13, 0x402204, 8, 0x400d60);
    CHECK(!st->regs[R_R13].address.valid,
          "unaligned store does not install an origin");
    env->regs[R_R13] = 0x402000;
    osprey_on_mem_load(env, CPU_NB_REGS + 5, 0x402200, 8, 0x400d70);

    /* Stage 2.4: every live pointer-width store to a canonical cell is
     * a valid F04 observation: the heap-pointer stores at 0x402100,
     * 0x402110, 0x402120, and the unaligned global-pointer store at
     * 0x402204 (F04 needs no alignment; only shadow installation
     * does).  The retired-heap and unknown-source stores at 0x402130
     * publish nothing, and no copy facts exist because no VALUE
     * channel was ever stored back to memory. */
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");
    CHECK(ctx->copy_facts->len == 0, "no copy facts published");
    CHECK(ctx->points_facts->len == 4,
          "live pointer stores publish exactly four F04 rows");
    OspreyPointsToFact *heap_row = NULL;
    OspreyPointsToFact *unaligned_row = NULL;
    for (guint i = 0; i < ctx->points_facts->len; i++) {
        OspreyPointsToFact *p = &g_array_index(ctx->points_facts,
                                               OspreyPointsToFact, i);
        if (p->pointer_chunk.address.offset == 0x2100) {
            heap_row = p;
        }
        if (p->pointer_chunk.address.offset == 0x2204) {
            unaligned_row = p;
        }
    }
    CHECK(heap_row != NULL &&
          heap_row->pointer_chunk.address.region.kind == 0 &&
          heap_row->pointer_chunk.size == 8 &&
          heap_row->target.region.kind == 1 &&
          heap_row->target.region.site_offset == 0x300 &&
          heap_row->target.offset == 0 &&
          heap_row->weak_numeric_evidence == 0,
          "F04 points at the exact canonical heap target");
    CHECK(unaligned_row != NULL &&
          unaligned_row->pointer_chunk.size == 8 &&
          unaligned_row->target.region.kind == 0 &&
          unaligned_row->target.offset == 0x2000,
          "unaligned pointer store publishes F04 without installing a slot");

    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

static void test_f02_ea_selection(void)
{
    reset_log();
    OspreyConfig c;
    OspreyContext *ctx;
    OspreySharedRun *run;
    CPUArchState *env;
    stage23_setup(&c, &ctx, &run, &env);
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    OspreyRegionId G, H, S;
    memset(&G, 0, sizeof(G));
    G.kind = OSPREY_REGION_GLOBAL;
    memset(&H, 0, sizeof(H));
    H.kind = OSPREY_REGION_HEAP_SITE;
    H.site_offset = 0x300;
    memset(&S, 0, sizeof(S));
    S.kind = OSPREY_REGION_STACK_FUNCTION;
    S.site_offset = 0x500;

    provenance_init();
    PtrTag t = provenance_create_object(0x10000, 64, 0x400300,
                                        PROV_PRODUCER_MALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_MALLOC,
            .site_pc = 0x400300,
            .requested_size = 64,
        };
        osprey_on_alloc_success(env, &obs, 0x10000, t.object_id, t.generation);
    }

    /* [base + disp]: base-only accepted with exact reconstruction. */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    env->regs[R_R12] = 0x10000;
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = -1;
    st->ea.scale = 0;
    st->ea.disp = 8;
    st->ea.base_val = 0x10000;
    st->ea.index_val = 0;
    st->ea.base_origin = st->regs[R_R12].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x10008, 1, 0x400e00, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 1, "base-only F02 emitted");
    {
        OspreyRunIter it;
        const void *rec;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = OSPREY_TABLE_BASE;
        CHECK(osprey_run_iter_next(&it, &rec) == 1, "base row present");
        const OspreyBaseFact *bf = rec;
        CHECK(bf->pc == 0xe00, "F02 access PC normalized");
        CHECK(bf->base.region.kind == OSPREY_REGION_HEAP_SITE &&
              bf->base.offset == 0, "F02 base H_site+0");
        CHECK(bf->chunk.address.offset == 8 && bf->chunk.size == 1,
              "F02 chunk H_site+8 size 1");
        CHECK(bf->prov_object_id == t.object_id &&
              bf->prov_generation == t.generation,
              "F02 carries provenance identity");
        CHECK(bf->producer_pc == 0x300,
              "F02 producer PC is the allocator site");
        CHECK(bf->sample_support == 1, "F02 support 1");
    }
    /* Consume-once: a second event without a fresh set-EA does not
     * reuse the snapshot. */
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x10010, 1, 0x400e00, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 1, "snapshot consumed once; no duplicate F02");
    CHECK(run->access_used == 2, "both accesses still record F01");

    /* Sole-base + untagged unscaled index: accepted. */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    memset(&st->regs[R_ECX], 0, sizeof(st->regs[R_ECX]));
    env->regs[R_ECX] = 3;
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = R_ECX;
    st->ea.scale = 0;
    st->ea.disp = 0;
    st->ea.base_val = 0x10000;
    st->ea.index_val = 3;
    st->ea.base_origin = st->regs[R_R12].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x10003, 1, 0x400e10, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 2, "base+untagged-index F02 emitted");
    {
        OspreyRunIter it;
        const void *rec;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = OSPREY_TABLE_BASE;
        bool found_indexed = false;
        while (osprey_run_iter_next(&it, &rec)) {
            const OspreyBaseFact *bf = rec;
            if (bf->pc == 0xe10) {
                found_indexed = true;
                CHECK(bf->base.offset == 0 &&
                      bf->chunk.address.offset == 3,
                      "indexed F02 base/chunk offsets");
            }
        }
        CHECK(found_indexed, "indexed F02 has its own access PC");
    }

    /* Index-only [index + disp]: no base register, shift zero. */
    memset(&st->regs[R_R12], 0, sizeof(st->regs[R_R12]));
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    env->regs[R_R12] = 0x10000;
    st->ea.valid = true;
    st->ea.base_reg = -1;
    st->ea.index_reg = R_R12;
    st->ea.scale = 0;
    st->ea.disp = 4;
    st->ea.index_val = 0x10000;
    st->ea.index_origin = st->regs[R_R12].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x10004, 1, 0x400e20, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 3, "index-only F02 emitted");

    /* F01-without-F02 near misses. */
    /* Two tagged origins. */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    install_addr_origin(st, R_ECX, 0x10000, &H, 0, 0x300);
    st->regs[R_ECX].address.prov_object_id = t.object_id;
    st->regs[R_ECX].address.prov_generation = t.generation;
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = R_ECX;
    st->ea.scale = 0;
    st->ea.base_val = 0x10000;
    st->ea.index_val = 0x10000;
    st->ea.base_origin = st->regs[R_R12].address;
    st->ea.index_origin = st->regs[R_ECX].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x20000, 1, 0x400e30, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 3, "two-origin form emits no F02");
    /* Scaled index (shift 1). */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    st->ea.valid = true;
    st->ea.base_reg = -1;
    st->ea.index_reg = R_R12;
    st->ea.scale = 1;
    st->ea.index_val = 0x10000;
    st->ea.index_origin = st->regs[R_R12].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x20000, 1, 0x400e40, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 3, "scaled index emits no F02");
    /* No origin. */
    memset(&st->regs[R_R12], 0, sizeof(st->regs[R_R12]));
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = -1;
    st->ea.base_val = 0x10000;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x10008, 1, 0x400e50, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 3, "no-origin form emits no F02");
    /* Concrete-value mismatch: snapshot says 0x10000, origin holds
     * 0x20000. */
    install_addr_origin(st, R_R12, 0x20000, &G, 0x2000, 0x600);
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = -1;
    st->ea.base_val = 0x10000;
    st->ea.base_origin = st->regs[R_R12].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x10008, 1, 0x400e60, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 3, "concrete-value mismatch emits no F02");
    CHECK(!st->regs[R_R12].address.valid,
          "value-mismatched snapshot invalidates authoritative channel");
    /* A valid-tag bit with a non-pointer width is not an untagged
     * operand and invalidates the authoritative channel. */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    st->regs[R_R12].address.width = 4;
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = -1;
    st->ea.base_val = 0x10000;
    st->ea.base_origin = st->regs[R_R12].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x10000, 1, 0x400e65, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 3, "width-mismatched origin emits no F02");
    CHECK(!st->regs[R_R12].address.valid,
          "width-mismatched snapshot invalidates authoritative channel");
    /* A heap origin without the authoritative provenance pair is invalid. */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = -1;
    st->ea.base_val = 0x10000;
    st->ea.base_origin = st->regs[R_R12].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x10000, 1, 0x400e66, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 3, "identity-free heap origin emits no F02");
    CHECK(!st->regs[R_R12].address.valid,
          "identity-free heap snapshot invalidates authoritative channel");
    /* Reconstruction mismatch: base_val + disp != addr. */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = -1;
    st->ea.disp = 8;
    st->ea.base_val = 0x10000;
    st->ea.base_origin = st->regs[R_R12].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x10020, 1, 0x400e70, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 3, "reconstruction mismatch emits no F02");
    /* Stale heap identity: freed object. */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    osprey_on_free_identity(env, t.object_id, t.generation, 0x400400);
    provenance_retire_object(0x10000);
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = -1;
    st->ea.disp = 0;
    st->ea.base_val = 0x10000;
    st->ea.base_origin = st->regs[R_R12].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x10000, 1, 0x400e80, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 3, "stale heap identity emits no F02");
    CHECK(!st->regs[R_R12].address.valid,
          "stale snapshot invalidates the authoritative register channel");
    /* Canonical region mismatch: origin G, chunk H. */
    install_addr_origin(st, R_R12, 0x10000, &G, 0x2000, 0x600);
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = -1;
    st->ea.base_val = 0x10000;
    st->ea.base_origin = st->regs[R_R12].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x10000, 1, 0x400e90, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 3, "canonical region mismatch emits no F02");
    /* Checked offset overflow: origin at INT64_MAX, delta +1. */
    install_addr_origin(st, R_R12, 0x10000, &G, INT64_MAX, 0x600);
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = -1;
    st->ea.base_val = 0x10000;
    st->ea.base_origin = st->regs[R_R12].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x10001, 1, 0x400ea0, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 3, "checked offset overflow emits no F02");

    /* Self-overwriting load: the pre-access snapshot is used, and the
     * loaded origin does not replace it.  R12 holds the pre-load heap
     * origin (t2) while the access reads 8 bytes through it. */
    PtrTag t2 = provenance_create_object(0x30000, 32, 0x400300,
                                         PROV_PRODUCER_MALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_MALLOC,
            .site_pc = 0x400300,
            .requested_size = 32,
        };
        osprey_on_alloc_success(env, &obs, 0x30000, t2.object_id, t2.generation);
    }
    install_addr_origin(st, R_R12, 0x30000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t2.object_id;
    st->regs[R_R12].address.prov_generation = t2.generation;
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = -1;
    st->ea.disp = 0;
    st->ea.base_val = 0x30000;
    st->ea.base_origin = st->regs[R_R12].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x30000, 8, 0x400eb0, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 4, "self-overwriting load F02 from pre-load origin");

    /* Mode-ineligible (16/32-bit) and segment-override modes emit
     * neither F01 nor F02 (gated in helper_sem_mem_access). */
    uint32_t access_before = run->access_used;
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = -1;
    st->ea.disp = 0;
    st->ea.base_val = 0x10000;
    st->ea.base_origin = st->regs[R_R12].address;
    st->ea_mode = MO_32;
    sem_mem_access(env, 0x10000, 1, 0x400ec0, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    st->ea.valid = true;
    st->ea.base_reg = R_R12;
    st->ea.index_reg = -1;
    st->ea.disp = 0;
    st->ea.base_val = 0x10000;
    st->ea.base_origin = st->regs[R_R12].address;
    st->ea_mode = MO_64 | (R_DS + 1) << 8; /* explicit segment override */
    sem_mem_access(env, 0x10000, 1, 0x400ed0, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 4, "truncating/segment modes emit no F02");
    CHECK(access_before == run->access_used, "mode-ineligible emits no F01");

    /* RIP-relative (-2) never decodes as a register: a base of -2 with
     * a valid-looking index register keeps only the index form. */
    install_addr_origin(st, R_ECX, 0x30000, &H, 0, 0x300);
    st->regs[R_ECX].address.prov_object_id = t2.object_id;
    st->regs[R_ECX].address.prov_generation = t2.generation;
    st->ea.valid = true;
    st->ea.base_reg = -2;
    st->ea.index_reg = R_ECX;
    st->ea.scale = 0;
    st->ea.disp = 0;
    st->ea.base_val = 0x402000;
    st->ea.index_val = 0x30000;
    st->ea.index_origin = st->regs[R_ECX].address;
    st->ea_mode = MO_64;
    sem_mem_access(env, 0x30000, 1, 0x400ee0, 0, SEM_OP_INTEGER,
                   SEM_INTERVAL_EXACT_WIDTH, SEM_PRODUCER_INTEGER_MODRM);
    CHECK(run->base_used == 5, "RIP-relative base + tagged index keeps index form");

    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");
    CHECK(ctx->copy_facts->len == 0 && ctx->points_facts->len == 0,
          "no copy/points rows in F02 fixture");

    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

/* ------------------------------------------------------------------ */
/* Stage 2.4: VALUE origins, F03/F04, shadow invalidation, modeled     */
/* copies, and copy/points merge/dump                                  */
/* ------------------------------------------------------------------ */

/* Install a VALUE origin directly (the load hook builds these; tests
 * that focus on store publication need a known-good channel). */
static void install_value_origin(OspreyCpuOriginState *st, int reg,
                                 target_ulong value, uint8_t width,
                                 const OspreyChunk *source) {
    OspreyValueOrigin *v = &st->regs[reg].value;
    memset(v, 0, sizeof(*v));
    v->valid = 1;
    v->width = width;
    v->concrete_value = value;
    if (source != NULL) {
        v->source = *source;
    }
}

static void fill_copy_fact(OspreyCopyFact *f, int64_t soff, uint64_t ssize,
                           int64_t doff, uint64_t dsize) {
    memset(f, 0, sizeof(*f));
    f->source.address.region.kind = OSPREY_REGION_GLOBAL;
    f->source.address.offset = soff;
    f->source.size = ssize;
    f->destination.address.region.kind = OSPREY_REGION_GLOBAL;
    f->destination.address.offset = doff;
    f->destination.size = dsize;
    f->sample_support = 1;
}

static void fill_points_fact(OspreyPointsToFact *f, int64_t cell_off,
                             uint64_t cell_size, int64_t tgt_off) {
    memset(f, 0, sizeof(*f));
    f->pointer_chunk.address.region.kind = OSPREY_REGION_GLOBAL;
    f->pointer_chunk.address.offset = cell_off;
    f->pointer_chunk.size = cell_size;
    f->target.region.kind = OSPREY_REGION_GLOBAL;
    f->target.offset = tgt_off;
    f->sample_support = 1;
    f->weak_numeric_evidence = 0;
}

/* Canonical 1/2/4/8-byte load origins, MOV/self-MOV/XCHG/self-XCHG
 * VALUE preservation, and every Stage 2.4 kill path. */
static void test_value_origin_creation_and_transfer(void)
{
    reset_log();
    OspreyConfig c;
    OspreyContext *ctx;
    OspreySharedRun *run;
    CPUArchState *env;
    stage23_setup(&c, &ctx, &run, &env);
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    OspreyRegionId G, H;
    memset(&G, 0, sizeof(G));
    G.kind = OSPREY_REGION_GLOBAL;
    memset(&H, 0, sizeof(H));
    H.kind = OSPREY_REGION_HEAP_SITE;
    H.site_offset = 0x300;

    /* Canonical 1/2/4/8-byte loads create VALUE origins with the
     * complete post-load GPR value and the exact source chunk. */
    for (int w = 0; w < 4; w++) {
        static const uint8_t widths[4] = { 1, 2, 4, 8 };
        static const uint8_t shifts[4] = { 0, 1, 2, 3 };
        uint8_t width = widths[w];
        target_ulong addr = 0x402100 + (target_ulong)(w * 0x10);
        target_ulong mem_val = 0x1122334455667788ULL &
            ((width == 8) ? ~0ULL
                          : ((1ULL << (width * 8)) - 1));
        env->regs[R_R12] = mem_val;
        osprey_on_mem_load(env, R_R12, addr, width, 0x400e00 + w);
        CHECK(st->regs[R_R12].value.valid &&
              st->regs[R_R12].value.width == width &&
              st->regs[R_R12].value.concrete_value == mem_val,
              "canonical width load creates VALUE origin");
        CHECK(st->regs[R_R12].value.source.address.region.kind == 0 &&
              st->regs[R_R12].value.source.address.offset ==
                  0x2100 + (int64_t)(w * 0x10) &&
              st->regs[R_R12].value.source.size == width,
              "VALUE source chunk exact for width");
        /* 32-bit zero-extension: the complete GPR value is recorded. */
        if (width == 4) {
            CHECK(st->regs[R_R12].value.concrete_value ==
                  (mem_val & 0xffffffffULL),
                  "dword load records zero-extended GPR value");
        }
        (void)shifts;
        osprey_on_reg_invalidate(env, R_R12);
    }

    /* A byte load followed by a byte store is a valid F03 flow;
     * full-width store after a smaller load is rejected (extension
     * bytes were not copied from the smaller source chunk). */
    env->regs[R_R12] = 0x7a;
    osprey_on_mem_load(env, R_R12, 0x402140, 1, 0x400e10);
    CHECK(st->regs[R_R12].value.valid, "byte load VALUE origin");
    env->regs[R_R12] = 0x7a;
    osprey_on_mem_store(env, R_R12, 0x402148, 1, 0x7a, 0x400d00);
    CHECK(run->copy_used == 1, "matching-width byte store publishes F03");
    env->regs[R_R12] = 0x7a;
    osprey_on_mem_store(env, R_R12, 0x402150, 8, 0x7a, 0x400d00);
    CHECK(run->copy_used == 1,
          "full-width store after byte load publishes no F03");

    /* Simultaneous ADDRESS+VALUE pointer reload: the shadow slot
     * restores ADDRESS while the load creates VALUE independently. */
    {
        provenance_init();
        PtrTag t = provenance_create_object(0x10000, 64, 0x400300,
                                            PROV_PRODUCER_MALLOC_RETURN);
        {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_MALLOC,
            .site_pc = 0x400300,
            .requested_size = 64,
        };
        osprey_on_alloc_success(env, &obs, 0x10000, t.object_id, t.generation);
    }
        install_addr_origin(st, R_R13, 0x10000, &H, 0, 0x300);
        st->regs[R_R13].address.prov_object_id = t.object_id;
        st->regs[R_R13].address.prov_generation = t.generation;
        env->regs[R_R13] = 0x10000;
        osprey_on_mem_store(env, R_R13, 0x402160, 8, 0x10000, 0x400d00);
        memset(&st->regs[R_R12], 0, sizeof(st->regs[R_R12]));
        env->regs[R_R12] = 0x10000;
        osprey_on_mem_load(env, R_R12, 0x402160, 8, 0x400e20);
        CHECK(st->regs[R_R12].address.valid &&
              st->regs[R_R12].address.canonical.offset == 0 &&
              st->regs[R_R12].address.prov_object_id == t.object_id,
              "pointer reload restores ADDRESS channel");
        CHECK(st->regs[R_R12].value.valid &&
              st->regs[R_R12].value.source.address.offset == 0x2160 &&
              st->regs[R_R12].value.concrete_value == 0x10000,
              "pointer reload also creates VALUE channel independently");
        /* Missing/stale ADDRESS slot never erases a valid VALUE. */
        memset(&st->regs[R_R12], 0, sizeof(st->regs[R_R12]));
        env->regs[R_R12] = 0x10000;
        osprey_on_mem_load(env, R_R12, 0x402168, 8, 0x400e21);
        CHECK(!st->regs[R_R12].address.valid &&
              st->regs[R_R12].value.valid &&
              st->regs[R_R12].value.source.address.offset == 0x2168,
              "missing slot keeps VALUE channel");
        /* A pointer-width load from an untagged cell must replace a
         * pre-existing ADDRESS channel even when the loaded number
         * happens to equal the old pointer.  Numeric coincidence is not
         * ADDRESS evidence. */
        install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
        st->regs[R_R12].address.prov_object_id = t.object_id;
        st->regs[R_R12].address.prov_generation = t.generation;
        env->regs[R_R12] = 0x10000;
        osprey_on_mem_load(env, R_R12, 0x402170, 8, 0x400e22);
        CHECK(!st->regs[R_R12].address.valid &&
              st->regs[R_R12].value.valid,
              "missing slot clears stale ADDRESS but keeps VALUE");

        /* F02 stale-origin cleanup is ADDRESS-only.  It must not erase
         * a valid VALUE channel created by the same successful load. */
        install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
        st->regs[R_R12].address.prov_object_id = t.object_id;
        st->regs[R_R12].address.prov_generation = t.generation + 1;
        install_value_origin(st, R_R12, 0x55, 4, NULL);
        memset(&st->ea, 0, sizeof(st->ea));
        st->ea.valid = 1;
        st->ea.base_reg = R_R12;
        st->ea.index_reg = -1;
        st->ea.base_val = 0x10000;
        st->ea.base_origin = st->regs[R_R12].address;
        osprey_on_mem_access_class(env, 0x402180, 4, 0x400e23, false,
                                   SEM_OP_INTEGER);
        CHECK(!st->regs[R_R12].address.valid &&
              st->regs[R_R12].value.valid,
              "stale F02 cleanup preserves independent VALUE");
    }

    /* Full-width MOV preserves VALUE with a concrete-value check;
     * self-MOV preserves once. */
    install_value_origin(st, R_R12, 0x1234, 4, NULL);
    env->regs[R_R12] = 0x1234;
    env->regs[R_R13] = 0x1234;
    osprey_on_reg_copy(env, R_R13, R_R12, 0x1234, 0x1234, 0x400e30);
    CHECK(st->regs[R_R13].value.valid &&
          st->regs[R_R13].value.concrete_value == 0x1234,
          "MOV64 preserves VALUE channel");
    env->regs[R_R12] = 0x1234;
    osprey_on_reg_copy(env, R_R12, R_R12, 0x1234, 0x1234, 0x400e31);
    CHECK(st->regs[R_R12].value.valid,
          "self-MOV preserves VALUE channel");
    /* Value-mismatched MOV kills the channel. */
    install_value_origin(st, R_R12, 0x1111, 4, NULL);
    env->regs[R_R12] = 0x1111;
    env->regs[R_R13] = 0x2222;
    osprey_on_reg_copy(env, R_R13, R_R12, 0x1111, 0x2222, 0x400e32);
    CHECK(!st->regs[R_R13].value.valid,
          "value-mismatched MOV kills VALUE channel");

    /* XCHG swaps VALUE channels under post-swap validation; self-XCHG
     * refreshes once.  A VALUE-only self-XCHG must not depend on an
     * unrelated ADDRESS channel. */
    install_value_origin(st, R_R12, 0x9999, 8, NULL);
    env->regs[R_R12] = 0x9999;
    osprey_on_reg_xchg(env, R_R12, R_R12, 0x9999, 0x9999, 0x400e3f);
    CHECK(st->regs[R_R12].value.valid &&
          st->regs[R_R12].value.concrete_value == 0x9999,
          "VALUE-only self-XCHG preserves its channel");
    install_value_origin(st, R_R12, 0xaaaa, 4, NULL);
    install_value_origin(st, R_R13, 0xbbbb, 8, NULL);
    env->regs[R_R12] = 0xbbbb;
    env->regs[R_R13] = 0xaaaa;
    osprey_on_reg_xchg(env, R_R12, R_R13, 0xbbbb, 0xaaaa, 0x400e40);
    CHECK(st->regs[R_R12].value.valid &&
          st->regs[R_R12].value.concrete_value == 0xbbbb &&
          st->regs[R_R12].value.width == 8 &&
          st->regs[R_R13].value.valid &&
          st->regs[R_R13].value.concrete_value == 0xaaaa &&
          st->regs[R_R13].value.width == 4,
          "XCHG swaps both VALUE channels");
    env->regs[R_R12] = 0xcccc;
    osprey_on_reg_xchg(env, R_R12, R_R12, 0xcccc, 0xcccc, 0x400e41);
    CHECK(!st->regs[R_R12].value.valid,
          "self-XCHG kills a value-mismatched channel");

    /* Kill paths: arithmetic, LEA, conditional/partial, caller-saved
     * clobber, context replacement, invalid register index. */
    install_value_origin(st, R_R12, 0x1000, 8, NULL);
    env->regs[R_R12] = 0x1008;
    osprey_on_reg_addsub_imm(env, R_R12, 8, 0x1000, 0x1008, 0x400e50);
    CHECK(!st->regs[R_R12].value.valid,
          "ADD/SUB immediate kills VALUE channel");
    install_value_origin(st, R_R12, 0x1000, 8, NULL);
    env->regs[R_R12] = 0x1008;
    osprey_on_reg_lea(env, R_R12, R_R12, 8, 0x1008, 0x1000, 0x400e51);
    CHECK(!st->regs[R_R12].value.valid, "LEA kills VALUE channel");
    install_value_origin(st, R_R12, 0x1000, 8, NULL);
    osprey_on_reg_invalidate(env, R_R12);
    CHECK(!st->regs[R_R12].value.valid,
          "generic register invalidation kills VALUE");
    install_value_origin(st, R_EAX, 0x1000, 8, NULL);
    install_value_origin(st, R_R12, 0x2000, 8, NULL);
    sem_clobber_caller_saved(env);
    CHECK(!st->regs[R_EAX].value.valid,
          "caller-saved clobber kills VALUE");
    CHECK(st->regs[R_R12].value.valid,
          "callee-saved register survives clobber");
    install_value_origin(st, R_R12, 0x1000, 8, NULL);
    sem_context_replace(env);
    CHECK(!st->regs[R_R12].value.valid &&
          !st->regs[R_R12].address.valid,
          "context replacement clears both channels");
    /* Out-of-image producer PC: transfer metadata fails closed. */
    install_value_origin(st, R_R12, 0x1000, 8, NULL);
    env->regs[R_R12] = 0x1000;
    osprey_on_reg_copy(env, R_R13, R_R12, 0x1000, 0x1000, 0x7f000000);
    CHECK(!st->regs[R_R13].value.valid,
          "out-of-image MOV metadata fails closed");
    /* Invalid register indices are bounds-safe. */
    osprey_on_mem_load(env, CPU_NB_REGS + 3, 0x402140, 8, 0x400e60);
    osprey_on_mem_store(env, CPU_NB_REGS + 3, 0x402148, 8, 0, 0x400d00);

    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

/* Ordinary F03/F04 publication: matching-width requirement, combined
 * channels, global/stack/live-heap targets, and the negative matrix. */
static void test_ordinary_f03_f04_publication(void)
{
    reset_log();
    OspreyConfig c;
    OspreyContext *ctx;
    OspreySharedRun *run;
    CPUArchState *env;
    stage23_setup(&c, &ctx, &run, &env);
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    OspreyRegionId G, H;
    memset(&G, 0, sizeof(G));
    G.kind = OSPREY_REGION_GLOBAL;
    memset(&H, 0, sizeof(H));
    H.kind = OSPREY_REGION_HEAP_SITE;
    H.site_offset = 0x300;

    provenance_init();
    PtrTag t = provenance_create_object(0x10000, 64, 0x400300,
                                        PROV_PRODUCER_MALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_MALLOC,
            .site_pc = 0x400300,
            .requested_size = 64,
        };
        osprey_on_alloc_success(env, &obs, 0x10000, t.object_id, t.generation);
    }

    /* Global-to-global F03 with a matching-width VALUE channel. */
    env->regs[R_R12] = 0x41414141;
    osprey_on_mem_load(env, R_R12, 0x402100, 4, 0x400f00);
    env->regs[R_R12] = 0x41414141;
    osprey_on_mem_store(env, R_R12, 0x402200, 4, 0x41414141, 0x400d00);
    CHECK(run->copy_used == 1, "G->G F03 published");
    {
        OspreyRunIter it;
        const void *rec;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = OSPREY_TABLE_COPY;
        CHECK(osprey_run_iter_next(&it, &rec) == 1, "copy row present");
        const OspreyCopyFact *cf = rec;
        CHECK(cf->source.address.offset == 0x2100 &&
              cf->source.size == 4 &&
              cf->destination.address.offset == 0x2200 &&
              cf->destination.size == 4 &&
              cf->sample_support == 1,
              "F03 source/destination chunks exact");
    }

    /* Stack source to heap destination F03. */
    {
        OspreyRegionId S;
        memset(&S, 0, sizeof(S));
        S.kind = OSPREY_REGION_STACK_FUNCTION;
        S.site_offset = 0x500;
        osprey_on_entrypoint(env, 0x400500, 0x7ffc0000);
        osprey_on_rsp_update(env, 0x7ffbff00, 0x400501);
        env->regs[R_R12] = 0xdeadbeefdeadbeefULL;
        osprey_on_mem_load(env, R_R12, 0x7ffbfe80, 8, 0x400f10);
        CHECK(st->regs[R_R12].value.valid &&
              st->regs[R_R12].value.source.address.region.kind == 2,
              "stack load VALUE origin");
        env->regs[R_R12] = 0xdeadbeefdeadbeefULL;
        osprey_on_mem_store(env, R_R12, 0x10000, 8, 0xdeadbeefdeadbeefULL, 0x400d00);
        CHECK(run->copy_used == 2, "S->H F03 published");
    }

    /* Simultaneous F03+F04: a tagged pointer value loaded from a cell
     * carries both channels; storing it to a second cell publishes
     * both facts. */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    {
        OspreyChunk src_cell;
        memset(&src_cell, 0, sizeof(src_cell));
        src_cell.address.region.kind = OSPREY_REGION_GLOBAL;
        src_cell.address.offset = 0x2100;
        src_cell.size = 8;
        install_value_origin(st, R_R12, 0x10000, 8, &src_cell);
    }
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402300, 8, 0x10000, 0x400d00);
    CHECK(run->copy_used == 3, "F03 for pointer-value store");
    CHECK(run->points_used == 1, "F04 for pointer-cell store");
    {
        OspreyRunIter it;
        const void *rec;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = OSPREY_TABLE_POINTS;
        CHECK(osprey_run_iter_next(&it, &rec) == 1, "points row present");
        const OspreyPointsToFact *pf = rec;
        CHECK(pf->pointer_chunk.address.offset == 0x2300 &&
              pf->pointer_chunk.size == 8 &&
              pf->target.region.kind == 1 &&
              pf->target.region.site_offset == 0x300 &&
              pf->target.offset == 0 &&
              pf->sample_support == 1 &&
              pf->weak_numeric_evidence == 0,
              "F04 points at live heap target");
    }

    /* Unaligned F04: publication allowed, shadow installation not.  The
     * register still carries the VALUE channel, so this store also
     * publishes F03 (alignment is irrelevant to the logical F03 fact). */
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402304, 8, 0x10000, 0x400d00);
    CHECK(run->points_used == 2,
          "unaligned pointer store publishes F04");
    CHECK(run->copy_used == 4,
          "unaligned pointer store still publishes F03");
    {
        OspreyRunIter it;
        const void *rec;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = OSPREY_TABLE_POINTS;
        CHECK(osprey_run_iter_next(&it, &rec) == 1, "first points row");
        CHECK(osprey_run_iter_next(&it, &rec) == 1, "second points row");
        const OspreyPointsToFact *pf = rec;
        CHECK(pf->pointer_chunk.address.offset == 0x2304,
              "unaligned F04 cell offset exact");
    }
    {
        OspreyRunIter it;
        const void *rec;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = OSPREY_TABLE_POINTS;
        (void)osprey_run_iter_next(&it, &rec);
        (void)osprey_run_iter_next(&it, &rec);
    }

    /* Negative matrix: null, numeric-map, stale generation, wrong
     * width, value mismatch, unresolved destination. */
    env->regs[R_R12] = 0;
    osprey_on_mem_store(env, R_R12, 0x402310, 8, 0, 0x400d00);
    CHECK(run->points_used == 2, "null store publishes no F04");
    env->regs[R_R12] = 0x7f0000000000ULL; /* unmapped numeric */
    osprey_on_mem_store(env, R_R12, 0x402318, 8, 0x7f0000000000ULL, 0x400d00);
    CHECK(run->points_used == 2, "numeric-map store publishes no F04");
    /* Stale generation: retire the object, keep the origin channel. */
    osprey_on_free_identity(env, t.object_id, t.generation, 0x400400);
    provenance_retire_object(0x10000);
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402320, 8, 0x10000, 0x400d00);
    CHECK(run->points_used == 2, "stale-generation store publishes no F04");
    /* One-byte-short store: F04 requires pointer width. */
    provenance_init();
    PtrTag t2 = provenance_create_object(0x20000, 64, 0x400300,
                                         PROV_PRODUCER_MALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_MALLOC,
            .site_pc = 0x400300,
            .requested_size = 64,
        };
        osprey_on_alloc_success(env, &obs, 0x20000, t2.object_id, t2.generation);
    }
    install_addr_origin(st, R_R12, 0x20000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t2.object_id;
    st->regs[R_R12].address.prov_generation = t2.generation;
    env->regs[R_R12] = 0x20000;
    osprey_on_mem_store(env, R_R12, 0x402328, 4, 0x20000, 0x400d00);
    CHECK(run->points_used == 2, "one-byte-short store publishes no F04");
    /* Value mismatch: register holds a different value than the tag. */
    env->regs[R_R12] = 0x20000;
    osprey_on_mem_store(env, R_R12, 0x402330, 8, 0x9999, 0x400d00);
    CHECK(run->points_used == 2, "value-mismatched store publishes no F04");
    /* A malformed VALUE record whose chunk width disagrees with its
     * channel width cannot authorize a copy fact. */
    OspreyChunk bad_source;
    memset(&bad_source, 0, sizeof(bad_source));
    bad_source.address.region = G;
    bad_source.address.offset = 0x2100;
    bad_source.size = 4;
    install_value_origin(st, R_R13, 0x1234, 8, &bad_source);
    osprey_on_mem_store(env, R_R13, 0x402338, 8, 0x1234, 0x400d00);
    CHECK(run->copy_used == 5,
          "F03 rejects inconsistent source and channel widths");

    OspreyStatus mst = osprey_parent_merge_sample(ctx, run);
    CHECK(mst == OSPREY_OK, "merge ok");
    /* Five F03 rows: G->G, S->H, 0x2300, unaligned 0x2304, and the
     * stale-generation store at 0x2320 (F03 is historical data flow;
     * retiring the source region instance does not falsify the past
     * load-to-store flow). */
    CHECK(ctx->copy_facts->len == 5, "five committed F03 rows");
    CHECK(ctx->points_facts->len == 2, "two committed F04 rows");
    CHECK(g_array_index(ctx->points_facts, OspreyPointsToFact, 1)
              .weak_numeric_evidence == 0,
          "no weak-numeric evidence in Stage 2.4");

    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

/* Exact sparse overlap invalidation: first/middle/final-byte overlap,
 * adjacent and zero-length no-ops, same-value partial writes, atomic,
 * MASKMOV selected bytes, external outputs, wrapping clears, and
 * exact reinstallation after a valid typed store. */
static void test_osprey_shadow_overlap_invalidation(void)
{
    reset_log();
    OspreyConfig c;
    OspreyContext *ctx;
    OspreySharedRun *run;
    CPUArchState *env;
    stage23_setup(&c, &ctx, &run, &env);
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    OspreyRegionId G, H;
    memset(&G, 0, sizeof(G));
    G.kind = OSPREY_REGION_GLOBAL;
    memset(&H, 0, sizeof(H));
    H.kind = OSPREY_REGION_HEAP_SITE;
    H.site_offset = 0x300;

    provenance_init();
    PtrTag t = provenance_create_object(0x10000, 64, 0x400300,
                                        PROV_PRODUCER_MALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_MALLOC,
            .site_pc = 0x400300,
            .requested_size = 64,
        };
        osprey_on_alloc_success(env, &obs, 0x10000, t.object_id, t.generation);
    }

    /* Install a live slot at 0x402100. */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402100, 8, 0x10000, 0x400d00);
    CHECK(g_hash_table_size(st->mem_slots) == 1, "slot installed");

    /* Helper pre-store attempts preserve OSPREY state; only the
     * complete post-success MASKMOV/multipart boundary invalidates. */
    sem_mem_helper_write_attempt(env, 0x402103, 1, SEM_OP_SIMD);
    CHECK(g_hash_table_size(st->mem_slots) == 1,
          "helper write attempt does not invalidate OSPREY early");
    st->ea_mode = MO_64;
    sem_mem_maskmov(env, 0x402100, 1u << 3, 8, 0x400d00,
                    SEM_OP_SIMD, SEM_INTERVAL_SPARSE,
                    SEM_PRODUCER_SIMD_MASKMOV);
    CHECK(g_hash_table_size(st->mem_slots) == 0,
          "successful MASKMOV invalidates selected bytes");
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402100, 8, 0x10000, 0x400d00);
    sem_mem_helper_write_attempt(env, 0x402100, 8, SEM_OP_PAIRED);
    CHECK(g_hash_table_size(st->mem_slots) == 1,
          "multipart write attempt preserves OSPREY state");
    st->ea_mode = MO_64;
    sem_mem_helper_access_part(env, 0x402100, 8, 0x400d00, true,
                               SEM_OP_PAIRED, SEM_INTERVAL_SPARSE,
                               SEM_PRODUCER_XSAVE_XSAVE, true);
    CHECK(g_hash_table_size(st->mem_slots) == 0,
          "successful multipart commit invalidates OSPREY state");
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402100, 8, 0x10000, 0x400d00);

    /* Overlap at the first byte: same-value byte write invalidates. */
    osprey_on_mem_store(env, CPU_NB_REGS, 0x402100, 1, 0, 0x400d00);
    CHECK(g_hash_table_size(st->mem_slots) == 0,
          "first-byte overlap removes slot (no byte-equality retention)");

    /* Reinstall, then middle and final byte overlap. */
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402100, 8, 0x10000, 0x400d00);
    osprey_on_mem_store(env, CPU_NB_REGS, 0x402104, 1, 0, 0x400d00);
    CHECK(g_hash_table_size(st->mem_slots) == 0,
          "middle-byte overlap removes slot");
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402100, 8, 0x10000, 0x400d00);
    osprey_on_mem_store(env, CPU_NB_REGS, 0x402107, 1, 0, 0x400d00);
    CHECK(g_hash_table_size(st->mem_slots) == 0,
          "final-byte overlap removes slot");

    /* Adjacent and zero-length writes preserve the slot. */
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402100, 8, 0x10000, 0x400d00);
    osprey_on_mem_store(env, CPU_NB_REGS, 0x402108, 8, 0, 0x400d00);
    CHECK(g_hash_table_size(st->mem_slots) == 1,
          "adjacent interval does not invalidate");
    osprey_on_mem_overwrite(env, 0x402100, 0);
    CHECK(g_hash_table_size(st->mem_slots) == 1,
          "zero-length overwrite is a no-op");

    /* Atomic RMW and unaligned qword writes invalidate overlap. */
    osprey_on_mem_store(env, CPU_NB_REGS, 0x402100, 8, 0x10000, 0x400d00);
    CHECK(g_hash_table_size(st->mem_slots) == 0,
          "unknown-source qword store invalidates");
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402100, 8, 0x10000, 0x400d00);
    osprey_on_mem_store(env, CPU_NB_REGS, 0x4020fe, 8, 0, 0x400d00);
    CHECK(g_hash_table_size(st->mem_slots) == 0,
          "unaligned qword spanning slot invalidates");

    /* Selected MASKMOV bytes and external outputs invalidate the exact
     * intervals they changed. */
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402100, 8, 0x10000, 0x400d00);
    osprey_on_mem_overwrite(env, 0x402103, 2);
    CHECK(g_hash_table_size(st->mem_slots) == 0,
          "external overwrite invalidates overlap");

    /* Wrapping interval clears the entire shadow. */
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402100, 8, 0x10000, 0x400d00);
    osprey_on_mem_store(env, R_R12, 0x402110, 8, 0x10000, 0x400d00);
    CHECK(g_hash_table_size(st->mem_slots) == 2, "two slots installed");
    osprey_on_mem_overwrite(env, (target_ulong)-8, 16);
    CHECK(g_hash_table_size(st->mem_slots) == 0,
          "wrapping interval clears the whole shadow");

    /* A valid aligned typed store reinstalls exactly one slot after
     * invalidation. */
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402100, 8, 0x10000, 0x400d00);
    CHECK(g_hash_table_size(st->mem_slots) == 1,
          "typed store reinstalls exactly one slot");
    {
        OspreyMemAddressOrigin *slot = g_hash_table_lookup(
            st->mem_slots, GSIZE_TO_POINTER(0x402100));
        CHECK(slot != NULL && slot->valid &&
              slot->concrete_value == 0x10000 &&
              slot->prov_object_id == t.object_id,
              "reinstalled slot carries the exact origin");
    }

    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

/* Modeled copies: exact F03 widths, overlapping memmove snapshots,
 * pointer-slot relocation + F04, strcpy NUL, strncpy padding, memset
 * overwrite-only, and rejection paths. */
static void test_modeled_copy_origins_and_facts(void)
{
    reset_log();
    OspreyConfig c;
    OspreyContext *ctx;
    OspreySharedRun *run;
    CPUArchState *env;
    stage23_setup(&c, &ctx, &run, &env);
    OspreyCpuOriginState *st = osprey_cpu_origin(env);
    OspreyRegionId H;
    memset(&H, 0, sizeof(H));
    H.kind = OSPREY_REGION_HEAP_SITE;
    H.site_offset = 0x300;

    provenance_init();
    PtrTag t = provenance_create_object(0x10000, 64, 0x400300,
                                        PROV_PRODUCER_MALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_MALLOC,
            .site_pc = 0x400300,
            .requested_size = 64,
        };
        osprey_on_alloc_success(env, &obs, 0x10000, t.object_id, t.generation);
    }

    /* Invalid copy classes are invalidation-only: they may remove a
     * destination slot but cannot authorize F03/F04 or relocation. */
    OspreyMemAddressOrigin *invalid_dst =
        g_new0(OspreyMemAddressOrigin, 1);
    invalid_dst->valid = 1;
    invalid_dst->width = sizeof(target_ulong);
    invalid_dst->concrete_value = 0x10000;
    invalid_dst->canonical.region = H;
    invalid_dst->prov_object_id = t.object_id;
    invalid_dst->prov_generation = t.generation;
    g_hash_table_replace(st->mem_slots, GSIZE_TO_POINTER(0x402200),
                         invalid_dst);
    sem_mem_copy(env, 0x402100, 0x402200, 8, (SemOpClass)-1);
    CHECK(run->copy_used == 0 && run->points_used == 0,
          "invalid copy class publishes no F03/F04");
    CHECK(g_hash_table_lookup(st->mem_slots,
                              GSIZE_TO_POINTER(0x402200)) == NULL,
          "invalid copy class still invalidates destination");

    /* Exact 13-byte memcpy F03 (source/destination canonical). */
    osprey_on_mem_copy(env, 0x402100, 0x402200, 13);
    CHECK(run->copy_used == 1, "memcpy 13-byte F03");
    {
        OspreyRunIter it;
        const void *rec;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = OSPREY_TABLE_COPY;
        CHECK(osprey_run_iter_next(&it, &rec) == 1, "copy row");
        const OspreyCopyFact *cf = rec;
        CHECK(cf->source.address.offset == 0x2100 &&
              cf->source.size == 13 &&
              cf->destination.address.offset == 0x2200 &&
              cf->destination.size == 13,
              "13-byte F03 exact");
    }

    /* Overlapping memmove: a live source slot inside the source range
     * is snapshotted before destination invalidation and relocated. */
    install_addr_origin(st, R_R12, 0x10000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = t.object_id;
    st->regs[R_R12].address.prov_generation = t.generation;
    env->regs[R_R12] = 0x10000;
    /* Store the pointer at 0x402108 (inside the 16-byte source range
     * starting at 0x402100). */
    osprey_on_mem_store(env, R_R12, 0x402108, 8, 0x10000, 0x400d00);
    CHECK(g_hash_table_size(st->mem_slots) == 1, "source slot live");
    /* memmove(buf+8, buf, 16): source [0x402100, 0x402110), dest
     * [0x402108, 0x402118).  The slot at 0x402108 relocates to
     * 0x402110. */
    osprey_on_mem_copy(env, 0x402100, 0x402108, 16);
    CHECK(run->copy_used == 2, "memmove F03");
    {
        OspreyMemAddressOrigin *slot = g_hash_table_lookup(
            st->mem_slots, GSIZE_TO_POINTER(0x402110));
        CHECK(slot != NULL && slot->valid &&
              slot->concrete_value == 0x10000 &&
              slot->prov_object_id == t.object_id,
              "overlapping memmove relocates snapshotted slot");
        CHECK(g_hash_table_lookup(st->mem_slots,
                                  GSIZE_TO_POINTER(0x402108)) == NULL,
              "destination-overlap slot removed");
    }
    /* F04 for the original cell store and the relocated canonical
     * destination cell. */
    CHECK(run->points_used == 2,
          "original store and relocated slot publish F04");

    /* strcpy includes the NUL: 4-byte F03 for "abc". */
    osprey_on_mem_copy(env, 0x402300, 0x402400, 4);
    CHECK(run->copy_used == 3, "strcpy 4-byte F03");
    {
        OspreyRunIter it;
        const void *rec;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = OSPREY_TABLE_COPY;
        (void)osprey_run_iter_next(&it, &rec);
        (void)osprey_run_iter_next(&it, &rec);
        CHECK(osprey_run_iter_next(&it, &rec) == 1, "strcpy copy row");
        const OspreyCopyFact *cf = rec;
        CHECK(cf->source.address.offset == 0x2300 &&
              cf->source.size == 4 &&
              cf->destination.address.offset == 0x2400,
              "strcpy F03 includes terminating NUL");
    }

    /* strncpy with padding: 4-byte F03 prefix + full-8 overwrite
     * invalidation (no copy row for the padding). */
    osprey_on_mem_copy(env, 0x402300, 0x402408, 4);   /* copied prefix */
    CHECK(run->copy_used == 4, "strncpy prefix F03");
    osprey_on_mem_overwrite(env, 0x40240c, 4);        /* padding tail */
    CHECK(run->copy_used == 4, "padding tail is not a copy");

    /* strncpy with no padding: full n F03. */
    osprey_on_mem_copy(env, 0x402300, 0x402410, 8);
    CHECK(run->copy_used == 5, "unpadded strncpy full F03");

    /* memset: overwrite-only. */
    osprey_on_mem_overwrite(env, 0x402420, 16);
    CHECK(run->copy_used == 5, "memset publishes no F03");

    /* Zero length: no fact, no shadow mutation. */
    osprey_on_mem_copy(env, 0x402100, 0x402200, 0);
    CHECK(run->copy_used == 5, "zero-length copy publishes no F03");

    /* Region-boundary crossing: a copy whose source spans the heap
     * region end cannot canonicalize as one chunk; no F03, but the
     * destination is still invalidated. */
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402500, 8, 0x10000, 0x400d00);
    /* Heap H+60..H+64: [0x1003c, 0x10040) crosses the 64-byte object
     * end (H+64) into unmapped space.  The destination [0x402504,
     * 0x40250c) overlaps the slot at 0x402500. */
    osprey_on_mem_copy(env, 0x1003c, 0x402504, 8);
    CHECK(run->copy_used == 5, "boundary-crossing copy publishes no F03");
    CHECK(g_hash_table_lookup(st->mem_slots,
                              GSIZE_TO_POINTER(0x402500)) == NULL,
          "boundary-crossing copy still invalidates destination");

    /* Stale source slot: retiring the heap identity drops the tag; no
     * relocation. */
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402700, 8, 0x10000, 0x400d00);
    CHECK(g_hash_table_lookup(st->mem_slots,
                              GSIZE_TO_POINTER(0x402700)) != NULL,
          "source slot installed before retirement");
    osprey_on_free_identity(env, t.object_id, t.generation, 0x400400);
    provenance_retire_object(0x10000);
    osprey_on_mem_copy(env, 0x402700, 0x402800, 8);
    CHECK(g_hash_table_lookup(st->mem_slots,
                              GSIZE_TO_POINTER(0x402708)) == NULL,
          "stale source slot not relocated");
    CHECK(g_hash_table_lookup(st->mem_slots,
                              GSIZE_TO_POINTER(0x402700)) == NULL,
          "stale source slot removed");
    /* The memmove-relocated slot (0x402110) predates the retirement
     * and stays live; only the stale source is gone. */
    CHECK(g_hash_table_size(st->mem_slots) == 1,
          "only the earlier relocated slot remains");

    /* Wrapping copy interval clears the destination shadow and
     * publishes no F03 (no canonical representation). */
    env->regs[R_R12] = 0x10000;
    osprey_on_mem_store(env, R_R12, 0x402900, 8, 0x10000, 0x400d00);
    osprey_on_mem_copy(env, 0x402910, (target_ulong)-16, 32);
    CHECK(g_hash_table_size(st->mem_slots) == 0,
          "wrapping copy clears destination shadow");
    CHECK(run->copy_used == 6, "wrapping copy publishes no F03");

    /* Relocation is complete for every live source slot.  A fixed local
     * snapshot cap must not drop the 65th tag or mutate disjoint source
     * metadata. */
    PtrTag many = provenance_create_object(0x11000, 64, 0x400300,
                                           PROV_PRODUCER_MALLOC_RETURN);
    {
        OspreyAllocatorObservation obs = {
            .kind = OSPREY_ALLOCATOR_MALLOC,
            .site_pc = 0x400300,
            .requested_size = 64,
        };
        osprey_on_alloc_success(env, &obs, 0x11000, many.object_id, many.generation);
    }
    install_addr_origin(st, R_R12, 0x11000, &H, 0, 0x300);
    st->regs[R_R12].address.prov_object_id = many.object_id;
    st->regs[R_R12].address.prov_generation = many.generation;
    env->regs[R_R12] = 0x11000;
    g_hash_table_remove_all(st->mem_slots);
    for (target_ulong i = 0; i < 65; i++) {
        osprey_on_mem_store(env, R_R12, 0x402a00 + i * 8, 8,
                            0x11000, 0x400d00);
    }
    CHECK(g_hash_table_size(st->mem_slots) == 65,
          "65 source pointer slots installed");
    uint32_t copies_before_many = run->copy_used;
    uint32_t points_before_many = run->points_used;
    osprey_on_mem_copy(env, 0x402a00, 0x402d00, 65 * 8);
    CHECK(run->copy_used == copies_before_many + 1,
          "large modeled copy publishes one full-width F03");
    CHECK(run->points_used == points_before_many + 65,
          "large modeled copy relocates every pointer slot");
    CHECK(g_hash_table_size(st->mem_slots) == 130,
          "large disjoint copy preserves all sources and destinations");
    CHECK(g_hash_table_lookup(st->mem_slots,
                              GSIZE_TO_POINTER(0x402a00 + 64 * 8)) != NULL &&
          g_hash_table_lookup(st->mem_slots,
                              GSIZE_TO_POINTER(0x402d00 + 64 * 8)) != NULL,
          "large modeled copy keeps and relocates the final slot");

    osprey_free(ctx);
    g_free(run);
    g_free(env);
}

/* Copy/points identity, Boolean support, prefix/suffix union, capacity
 * failure, canonical sort order, and exact row schema. */
static void test_copy_points_merge_and_dump(void)
{
    reset_log();
    CHECK(OSPREY_SHARED_VERSION == 10u,
          "shared format version 10 (Stage 2.5)");
    CHECK(sizeof(OspreyValueOrigin) > 8,
          "VALUE origin carries the full source chunk record");

    OspreyConfig c = test_config();
    snprintf(c.dump_file, sizeof(c.dump_file), "/tmp/osprey_cp_dump.txt");
    unlink(c.dump_file);
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);

    /* Duplicate insertion in both orders merges in place; support stays
     * Boolean inside one sample. */
    OspreyCopyFact cf1, cf2;
    fill_copy_fact(&cf1, 0x2100, 8, 0x2200, 8);
    fill_copy_fact(&cf2, 0x2110, 4, 0x2210, 4);
    CHECK(osprey_table_insert_copy(run, &cf1) == 1, "insert copy 1");
    CHECK(osprey_table_insert_copy(run, &cf2) == 1, "insert copy 2");
    CHECK(osprey_table_insert_copy(run, &cf1) == 0,
          "copy duplicate merges in place");
    CHECK(run->copy_used == 2, "two unique copy records");
    OspreyPointsToFact pf1, pf2;
    fill_points_fact(&pf1, 0x2200, 8, 0x3000);
    fill_points_fact(&pf2, 0x2210, 8, 0x3010);
    CHECK(osprey_table_insert_points(run, &pf1) == 1, "insert points 1");
    CHECK(osprey_table_insert_points(run, &pf2) == 1, "insert points 2");
    CHECK(osprey_table_insert_points(run, &pf1) == 0,
          "points duplicate merges in place");
    CHECK(run->points_used == 2, "two unique points records");

    /* Signed offsets print as two's-complement hex.  Within one stack
     * region the positive row therefore sorts before the -8 row. */
    OspreyCopyFact cf_stack_pos, cf_stack_neg;
    fill_copy_fact(&cf_stack_pos, 8, 8, 0x18, 8);
    cf_stack_pos.source.address.region.kind = OSPREY_REGION_STACK_FUNCTION;
    cf_stack_pos.source.address.region.site_offset = 0x500;
    cf_stack_pos.destination.address.region =
        cf_stack_pos.source.address.region;
    cf_stack_neg = cf_stack_pos;
    cf_stack_neg.source.address.offset = -8;
    cf_stack_neg.destination.address.offset = -0x18;
    CHECK(osprey_table_insert_copy(run, &cf_stack_pos) == 1,
          "insert positive stack copy");
    CHECK(osprey_table_insert_copy(run, &cf_stack_neg) == 1,
          "insert negative stack copy");
    OspreyPointsToFact pf_stack_pos, pf_stack_neg;
    fill_points_fact(&pf_stack_pos, 8, 8, 0x18);
    pf_stack_pos.pointer_chunk.address.region.kind =
        OSPREY_REGION_STACK_FUNCTION;
    pf_stack_pos.pointer_chunk.address.region.site_offset = 0x500;
    pf_stack_pos.target.region = pf_stack_pos.pointer_chunk.address.region;
    pf_stack_neg = pf_stack_pos;
    pf_stack_neg.pointer_chunk.address.offset = -8;
    pf_stack_neg.target.offset = -0x18;
    CHECK(osprey_table_insert_points(run, &pf_stack_pos) == 1,
          "insert positive stack points");
    CHECK(osprey_table_insert_points(run, &pf_stack_neg) == 1,
          "insert negative stack points");
    CHECK(run->copy_used == 4 && run->points_used == 4,
          "four unique copy and points records");

    /* Prefix/suffix union: the same copy fact in both families commits
     * once with one support. */
    OspreySharedRun *run2 = new_run(&c);
    CHECK(osprey_table_insert_copy(run2, &cf1) == 1, "prefix copy");
    CHECK(osprey_shared_run_freeze_prefix(ctx, run2),
          "prefix freeze with copy fact");
    osprey_shared_run_prepare(ctx, run2, 1);
    CHECK(osprey_table_insert_copy(run2, &cf1) == 1,
          "suffix re-observation of prefix copy");
    CHECK(run2->copy_used == 1, "union has one copy record");
    CHECK(osprey_parent_merge_sample(ctx, run2) == OSPREY_OK,
          "prefix/suffix copy union merges");
    CHECK(ctx->copy_facts->len == 1 &&
          g_array_index(ctx->copy_facts, OspreyCopyFact, 0)
                  .sample_support == 1,
          "prefix/suffix duplicate contributes one support");
    g_free(run2);

    /* Capacity exhaustion rejects fail-closed. */
    reset_log();
    OspreyConfig c2 = test_config();
    c2.max_facts = 1;
    OspreyContext *ctx2 = osprey_new(&c2);
    OspreySharedRun *run3 = new_run(&c2);
    OspreyCopyFact cf3;
    fill_copy_fact(&cf3, 0x3000, 8, 0x3100, 8);
    CHECK(osprey_table_insert_copy(run3, &cf3) == 1, "copy fills cap");
    OspreyCopyFact cf4;
    fill_copy_fact(&cf4, 0x3010, 8, 0x3110, 8);
    CHECK(osprey_table_insert_copy(run3, &cf4) == -1,
          "second copy exceeds cap");
    CHECK(run3->overflow == 1, "copy cap overflow sticky");
    CHECK(osprey_parent_merge_sample(ctx2, run3) ==
              OSPREY_INCOMPLETE_FACTS,
          "copy cap merge rejects fail-closed");
    CHECK(ctx2->copy_facts->len == 0, "copy cap no partial merge");
    osprey_free(ctx2);
    g_free(run3);

    /* Canonical dump: copy/points rows sorted by every printed field
     * with the exact 10-token schema and zero weak-numeric evidence. */
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK,
          "dump merge ok");
    FILE *f = fopen(c.dump_file, "r");
    CHECK(f != NULL, "dump file written");
    if (f != NULL) {
        char line[256];
        char copy_lines[8][256];
        char points_lines[8][256];
        int n_copy = 0, n_points = 0;
        while (fgets(line, sizeof(line), f)) {
            if (strncmp(line, "copy ", 5) == 0 && n_copy < 8) {
                snprintf(copy_lines[n_copy++], sizeof(copy_lines[0]),
                         "%s", line);
            }
            if (strncmp(line, "points ", 7) == 0 && n_points < 8) {
                snprintf(points_lines[n_points++], sizeof(points_lines[0]),
                         "%s", line);
            }
        }
        fclose(f);
        CHECK(n_copy == 4, "dump has four copy rows");
        CHECK(n_points == 4, "dump has four points rows");
        /* Sorted by all printed fields.  Global rows precede stack rows;
         * inside S_0x500, +8 precedes -8 because the printed hex order
         * compares the uint64_t representation.  cf1 was committed once
         * by the prefix/suffix union and once by the dump merge, so its
         * support is 2. */
        CHECK(n_copy == 4 &&
              strstr(copy_lines[0], "0 0 2100 8 0 0 2200 8 2") != NULL &&
              strstr(copy_lines[1], "0 0 2110 4 0 0 2210 4 1") != NULL &&
              strstr(copy_lines[2], "2 500 8 8 2 500 18 8 1") != NULL &&
              strstr(copy_lines[3],
                     "2 500 fffffffffffffff8 8 2 500 "
                     "ffffffffffffffe8 8 1") != NULL,
              "copy rows use exact two's-complement field order");
        CHECK(n_points == 4 &&
              strstr(points_lines[0], "0 0 2200 8 0 0 3000 1 0") != NULL &&
              strstr(points_lines[1], "0 0 2210 8 0 0 3010 1 0") != NULL &&
              strstr(points_lines[2], "2 500 8 8 2 500 18 1 0") != NULL &&
              strstr(points_lines[3],
                     "2 500 fffffffffffffff8 8 2 500 "
                     "ffffffffffffffe8 1 0") != NULL,
              "points rows use exact two's-complement field order");
    }
    unlink(c.dump_file);

    osprey_free(ctx);
    g_free(run);
}

static void test_base_fact_producer_merge(void)
{
    reset_log();
    /* The version-10 base record carries producer_pc as deterministic
     * audit metadata. */
    CHECK(OSPREY_SHARED_VERSION == 10u, "shared format version 10");
    CHECK(offsetof(OspreyBaseFact, producer_pc) <
              offsetof(OspreyBaseFact, sample_support),
          "producer_pc precedes sample_support in the fixed record");

    OspreyConfig c = test_config();
    OspreyContext *ctx = osprey_new(&c);
    OspreySharedRun *run = new_run(&c);

    OspreyBaseFact b1, b2;
    memset(&b1, 0, sizeof(b1));
    b1.pc = 0x100;
    b1.chunk.address.region.kind = OSPREY_REGION_GLOBAL;
    b1.chunk.address.offset = 0x2000;
    b1.chunk.size = 8;
    b1.base.region.kind = OSPREY_REGION_GLOBAL;
    b1.base.offset = 0x2000;
    b1.producer_pc = 0x50;
    b1.sample_support = 1;
    b2 = b1;
    b2.producer_pc = 0x30;

    /* Logical duplicates with different producer PCs merge once and
     * retain the numerically smallest producer PC. */
    CHECK(osprey_table_insert_base(run, &b1) == 1, "insert b1");
    CHECK(osprey_table_insert_base(run, &b2) == 0,
          "logical duplicate merges in place");
    {
        OspreyRunIter it;
        const void *rec;
        memset(&it, 0, sizeof(it));
        it.run = run;
        it.table = OSPREY_TABLE_BASE;
        CHECK(osprey_run_iter_next(&it, &rec) == 1,
              "one base record after duplicate");
        const OspreyBaseFact *bf = rec;
        CHECK(bf->producer_pc == 0x30,
              "duplicate merge retains smallest producer PC");
        CHECK(bf->sample_support == 1, "Boolean support preserved");
    }
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "merge ok");
    CHECK(ctx->base_facts->len == 1, "one committed base fact");
    {
        OspreyBaseFact *first = &g_array_index(ctx->base_facts,
                                               OspreyBaseFact, 0);
        CHECK(first->producer_pc == 0x30,
              "parent merge retains smallest producer PC");
    }

    /* Zero producer PC wins over any nonzero value. */
    memset(&b1, 0, sizeof(b1));
    b1.pc = 0x200;
    b1.chunk.address.region.kind = OSPREY_REGION_GLOBAL;
    b1.chunk.address.offset = 0x2010;
    b1.chunk.size = 8;
    b1.base = b1.chunk.address;
    b1.producer_pc = 0x40;
    b1.sample_support = 1;
    CHECK(osprey_table_insert_base(run, &b1) == 1, "insert zero test b1");
    b2 = b1;
    b2.producer_pc = 0;
    CHECK(osprey_table_insert_base(run, &b2) == 0,
          "zero-producer duplicate merges in place");
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK, "second merge ok");
    CHECK(ctx->base_facts->len == 2, "two committed base facts");
    for (guint i = 0; i < ctx->base_facts->len; i++) {
        OspreyBaseFact *d = &g_array_index(ctx->base_facts,
                                           OspreyBaseFact, i);
        if (d->pc == 0x200) {
            CHECK(d->producer_pc == 0, "zero producer PC wins");
            CHECK(d->sample_support == 1,
                  "new fact in sample 2 has support 1");
        }
        if (d->pc == 0x100) {
            CHECK(d->sample_support == 2,
                  "repeated fact gains one support per sample");
        }
    }

    /* Prefix/suffix order independence: a prefix fact with the larger
     * producer PC merges into an earlier committed smaller-PC fact
     * without changing the dump. */
    memset(&b1, 0, sizeof(b1));
    b1.pc = 0x300;
    b1.chunk.address.region.kind = OSPREY_REGION_GLOBAL;
    b1.chunk.address.offset = 0x2020;
    b1.chunk.size = 8;
    b1.base = b1.chunk.address;
    b1.producer_pc = 0x60;
    b1.sample_support = 1;
    CHECK(osprey_table_insert_base(run, &b1) == 1, "prefix insert");
    CHECK(osprey_shared_run_freeze_prefix(ctx, run), "prefix freeze");
    CHECK(osprey_parent_merge_sample(ctx, run) == OSPREY_OK,
          "prefix merge ok");
    {
        OspreyBaseFact *d = NULL;
        for (guint i = 0; i < ctx->base_facts->len; i++) {
            OspreyBaseFact *cand = &g_array_index(ctx->base_facts,
                                                  OspreyBaseFact, i);
            if (cand->pc == 0x300) {
                d = cand;
            }
        }
        CHECK(d != NULL, "prefix fact committed");
        if (d != NULL) {
            CHECK(d->producer_pc == 0x60, "prefix producer PC retained");
            CHECK(d->sample_support == 1, "prefix support once");
        }
    }

    osprey_free(ctx);
    g_free(run);
}
