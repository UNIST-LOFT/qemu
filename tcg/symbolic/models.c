#include "../../linux-user/provenance.h"

#define MODEL_PARSE_MAX_INPUT 64


/* ---- Guest range validation (Phase 3) ----
 * libc-model bodies must not read or classify guest memory that the real
 * libc call could not complete: a host-side scan over an invalid guest
 * range would fabricate access or bypass the real fault. A range is valid
 * only when every page it touches is mapped with the required permission.
 * Under the single-threaded guest contract a subsequent model read cannot
 * race with unmapping, so the follow-up model work is then safe. */

static inline bool prov_range_valid(target_ulong addr, target_ulong size,
                                    int flags)
{
    int type = flags == PAGE_READ ? VERIFY_READ : VERIFY_WRITE;

    if (size != 0 && addr > (target_ulong)-1 - (size - 1)) {
        return false;
    }
    return access_ok(type, addr, size);
}

static inline bool prov_range_readable(target_ulong addr, target_ulong size)
{
    return prov_range_valid(addr, size, PAGE_READ);
}

static inline bool prov_range_writable(target_ulong addr, target_ulong size)
{
    return prov_range_valid(addr, size, PAGE_READ | PAGE_WRITE);
}

/* Page-probing string scan: prefix length up to the first NUL, or limit for
 * a bounded string operation.  An unbounded scan does the same work as the
 * libc operation rather than imposing an arbitrary cap that would hide long
 * modeled accesses from provenance. */
static inline size_t prov_str_scan(const char *s, size_t limit, bool bounded,
                                   bool *probe_ok)
{
    *probe_ok = true;
    if (s == NULL) {
        *probe_ok = false;
        return 0;
    }
    if (bounded && limit == 0) {
        return 0;
    }
    size_t len = 0;
    target_ulong addr = (target_ulong)s;
    for (;;) {
        size_t chunk = TARGET_PAGE_SIZE - (addr & ~TARGET_PAGE_MASK);
        if (bounded && chunk > limit - len) {
            chunk = limit - len;
        }
        if (!access_ok(VERIFY_READ, addr, chunk)) {
            *probe_ok = false;
            return len;
        }
        const char *p = g2h(addr);
        for (size_t i = 0; i < chunk; i++) {
            if (p[i] == '\0') {
                return len + i;
            }
        }
        len += chunk;
        if (bounded && len == limit) {
            return len;
        }
        if (addr > (target_ulong)-1 - chunk) {
            *probe_ok = false;
            return len;
        }
        addr += chunk;
    }
}

/* Scan only logically consumed bytes.  Page probes precede each host read;
 * optimized guest implementations may overfetch, but their summaries do not. */
static bool prov_compare_scan(target_ulong a, target_ulong b, size_t limit,
                              bool bounded, bool strings, size_t *width,
                              int *result)
{
    *width = 0;
    *result = 0;
    while (!bounded || *width < limit) {
        size_t i = *width;
        if (a > (target_ulong)-1 - i || b > (target_ulong)-1 - i)
            return false;
        target_ulong aa = a + i, bb = b + i;
        size_t chunk = MIN(TARGET_PAGE_SIZE - (aa & ~TARGET_PAGE_MASK),
                            TARGET_PAGE_SIZE - (bb & ~TARGET_PAGE_MASK));
        if (bounded) chunk = MIN(chunk, limit - i);
        if (!prov_range_readable(aa, chunk) ||
            !prov_range_readable(bb, chunk)) return false;
        const unsigned char *xbytes = g2h(aa), *ybytes = g2h(bb);
        for (size_t j = 0; j < chunk; ++j) {
            unsigned char x = xbytes[j], y = ybytes[j];
            ++*width;
            *result = (int)x - (int)y;
            if (x != y || (strings && x == 0)) return true;
        }
    }
    return true;
}

static Expr* pending_model_return_expr = NULL;

static inline void set_pending_model_return_expr(Expr* expr)
{
    pending_model_return_expr = expr;
}

static inline Expr* take_pending_model_return_expr(void)
{
    Expr* expr = pending_model_return_expr;
    pending_model_return_expr = NULL;
    return expr;
}

static inline void clear_call_args_temps(void)
{
    if (!symbolic_mode) return;
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "rax"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "rdi"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "rsi"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "rdx"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "rcx"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "r8"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "r9"))] = 0;
}

static void add_query_with_model(Expr *q, uintptr_t address, MODEL_T model,
                                 const char *msg)
{
    (void)publish_model_query(q, address, model, msg);
}

// clear xmm registers
static inline void clear_xmm_regs(CPUX86State* env)
{
    if (!symbolic_mode) return;
    int          i, nb_xmm_regs;

    if (env->hflags & HF_CS64_MASK) {
        nb_xmm_regs = 16;
    } else {
        nb_xmm_regs = 8;
    }

    for (i = 0; i < nb_xmm_regs; i++) {
        clear_mem((uintptr_t)&(env->xmm_regs[i]), XMM_BYTES);
    }
}

static inline Expr* build_expr(Expr** exprs, void* addr, size_t size)
{
    Expr* dst_expr = NULL;
    for (size_t i = 0; i < size; i++) {
        size_t idx = i; // size - i - 1;
        if (i == 0) {
            dst_expr = exprs ? exprs[idx] : NULL;
            if (dst_expr == NULL) {
                dst_expr           = new_expr();
                dst_expr->opkind   = IS_CONST;
                uint8_t* byte_addr = ((uint8_t*)addr) + idx;
                uint8_t  byte      = *byte_addr;
                dst_expr->op1      = (Expr*)((uintptr_t)byte);
            }
        } else {
            Expr* n_expr   = new_expr();
            n_expr->opkind = CONCAT8L;
            if (exprs == NULL || exprs[idx] == NULL) {
                // fetch the concrete value, embed it in the expr
                uint8_t* byte_addr   = ((uint8_t*)addr) + idx;
                uint8_t  byte        = *byte_addr;
                n_expr->op1          = (Expr*)((uintptr_t)byte);
                n_expr->op1_is_const = 1;
            } else {
                n_expr->op1 = exprs[idx];
            }
            n_expr->op2 = dst_expr;

            dst_expr = n_expr;
        }
    }

    // print_expr(dst_expr);
    return dst_expr;
}

static inline int model_is_space(char c)
{
    return c == ' ' || c == '\t' || c == '\n' || c == '\r' ||
           c == '\f' || c == '\v';
}

static inline int model_digit_for_base(char c, int base)
{
    int digit = -1;
    if (c >= '0' && c <= '9') {
        digit = c - '0';
    } else if (c >= 'a' && c <= 'z') {
        digit = 10 + (c - 'a');
    } else if (c >= 'A' && c <= 'Z') {
        digit = 10 + (c - 'A');
    }

    if (digit < 0 || digit >= base) {
        return -1;
    }
    return digit;
}

static inline size_t model_numeric_span(const char* s, int base,
                                        int* used_base_out)
{
    size_t i = 0;
    int used_base = base;

    while (s[i] && model_is_space(s[i]) && i < MODEL_PARSE_MAX_INPUT) {
        i++;
    }

    if (s[i] == '+' || s[i] == '-') {
        i++;
    }

    if (used_base == 0) {
        used_base = 10;
        if (s[i] == '0') {
            used_base = 8;
            if ((s[i + 1] == 'x' || s[i + 1] == 'X')) {
                used_base = 16;
            }
        }
    }

    if (used_base == 16 && s[i] == '0' &&
        (s[i + 1] == 'x' || s[i + 1] == 'X')) {
        i += 2;
    }

    while (s[i] && i < MODEL_PARSE_MAX_INPUT) {
        if (model_digit_for_base(s[i], used_base) < 0) {
            break;
        }
        i++;
    }

    if (used_base_out != NULL) {
        *used_base_out = used_base;
    }
    return i;
}

static inline int model_has_symbolic_bytes(Expr** exprs, size_t len)
{
    if (exprs == NULL) {
        return 0;
    }
    for (size_t i = 0; i < len; i++) {
        if (exprs[i] != NULL) {
            return 1;
        }
    }
    return 0;
}

static inline Expr* model_build_return_expr(Expr* input_expr,
                                            uintptr_t concrete_value,
                                            uintptr_t meta)
{
    Expr* ret_expr = new_expr();
    ret_expr->opkind = MODEL;
    ret_expr->op1 = input_expr;
    SET_EXPR_CONST_OP(ret_expr->op2, ret_expr->op2_is_const,
                      concrete_value);
    SET_EXPR_CONST_OP(ret_expr->op3, ret_expr->op3_is_const, meta);
    return ret_expr;
}

static inline int model_strcmp(CPUX86State* env, uintptr_t pc, uintptr_t n,
                               bool bounded)
{
    int mode = 2;
    char* s1 = (char *)(uintptr_t)env->regs[R_EDI];
    char* s2 = (char *)(uintptr_t)env->regs[R_ESI];

    if (bounded && n == 0) {
        return mode;
    }
    if (s1 == NULL || s2 == NULL) {
        return 0;
    }

    size_t width;
    int res;
    if (!prov_compare_scan((target_ulong)s1, (target_ulong)s2, n, bounded,
                           true, &width, &res)) return 0;
    size_t s1_width = width, s2_width = width;
    size_t s1_len = width - (*(unsigned char *)g2h((target_ulong)s1 + width - 1) == 0);
    size_t s2_len = width - (*(unsigned char *)g2h((target_ulong)s2 + width - 1) == 0);
    /* memcheck-only: the host string functions read guest memory without
     * interval checks; validate the read ranges here (access pc = caller). */
    if (binradar_memcheck_enabled) {
        provenance_model_check_access(env, (target_ulong)s1, s1_width, pc,
                                      R_EDI);
        provenance_model_check_access(env, (target_ulong)s2, s2_width, pc,
                                      R_ESI);
    }

    if (!symbolic_mode) return mode;
    bool s1_exprs_allocated = false, s2_exprs_allocated = false;
    Expr** s1_exprs = get_expr_addr_span((uintptr_t)s1, s1_width,
                                         &s1_exprs_allocated);
    Expr** s2_exprs = get_expr_addr_span((uintptr_t)s2, s2_width,
                                         &s2_exprs_allocated);

    if (s1_exprs == NULL && s2_exprs == NULL) {
        return mode;
    }

    int s1_is_not_null = 0;
    if (s1_exprs) {
        for (size_t i = 0; i < s1_width && s1_is_not_null == 0; i++) {
            s1_is_not_null |= s1_exprs[i] != NULL;
        }
    }

    int s2_is_not_null = 0;
    if (s2_exprs) {
        for (size_t i = 0; i < s2_width && s2_is_not_null == 0; i++) {
            s2_is_not_null |= s2_exprs[i] != NULL;
        }
    }

    if (!s1_is_not_null && !s2_is_not_null) {
        if (s1_exprs_allocated) {
            g_free(s1_exprs);
        }
        if (s2_exprs_allocated) {
            g_free(s2_exprs);
        }
        return mode;
    }

    Expr* s1_expr = build_expr(s1_exprs, s1, s1_width);
    Expr* s2_expr = build_expr(s2_exprs, s2, s2_width);
    if (s1_exprs_allocated) {
        g_free(s1_exprs);
    }
    if (s2_exprs_allocated) {
        g_free(s2_exprs);
    }

    uint64_t v = 0;
    v          = PACK_0(v, res);
    v          = PACK_1(v, s1_len);
    v          = PACK_2(v, s2_len);
    v          = PACK_3(v, bounded ? n : 0);

    Expr* e = new_expr();
    e->opkind = MODEL;
    e->op1 = s1_expr;
    e->op2 = s2_expr;
    SET_EXPR_CONST_OP(e->op3, e->op3_is_const, v);

    add_query_with_model(e, pc, MODEL_STRCMP, "model_strcmp");
    // next_query[0].query   = e;
    // next_query[0].address = pc;
    // next_query[0].model   = MODEL_STRCMP;
    // next_query++;

    return mode;
}

static inline int model_strlen_scanned(CPUX86State* env, uintptr_t pc,
                                       uintptr_t n, bool bounded, int reg,
                                       size_t s1_len)
{
    int mode = 2;
    char* s1 = (char *)(uintptr_t)env->regs[reg];

    if (bounded && n == 0) {
        return mode;
    }
    if (s1 == NULL) {
        return 0;
    }

    size_t len = !bounded || s1_len < n ? s1_len + 1 : s1_len;
    /* memcheck-only: the host string function reads guest memory without
     * interval checks; validate the read range here (access pc = caller). */
    if (binradar_memcheck_enabled) {
        provenance_model_check_access(env, (target_ulong)s1, len, pc, reg);
    }
    if (!symbolic_mode) return mode;
    bool s1_exprs_allocated = false;
    Expr** s1_exprs = get_expr_addr_span((uintptr_t)s1, len,
                                         &s1_exprs_allocated);

    if (s1_exprs == NULL) {
        return mode;
    }

    int s1_is_not_null = 0;
    for (size_t i = 0; i < len && s1_is_not_null == 0; i++) {
        s1_is_not_null |= s1_exprs[i] != NULL;
    }

    if (!s1_is_not_null) {
        if (s1_exprs_allocated) {
            g_free(s1_exprs);
        }
        return mode;
    }

    Expr* s1_expr = build_expr(s1_exprs, s1, len);
    if (s1_exprs_allocated) {
        g_free(s1_exprs);
    }

    uint64_t v = 0;
    v          = PACK_0(v, s1_len);
    v          = PACK_1(v, bounded ? n : 0);

    Expr* e = new_expr();
    e->opkind = MODEL;
    e->op1 = s1_expr;
    SET_EXPR_CONST_OP(e->op2, e->op2_is_const, v);

    add_query_with_model(e, pc, MODEL_STRLEN, "model_strlen");
    // next_query[0].query   = e;
    // next_query[0].address = pc;
    // next_query[0].model   = MODEL_STRLEN;
    // next_query++;

    return mode;
}

static inline int model_strlen(CPUX86State* env, uintptr_t pc, uintptr_t n,
                               bool bounded, int reg)
{
    if (bounded && n == 0) return 2;
    bool ok;
    size_t len = prov_str_scan((const char *)(uintptr_t)env->regs[reg],
                               n, bounded, &ok);
    return ok ? model_strlen_scanned(env, pc, n, bounded, reg, len) : 0;
}

static inline int model_memchr(CPUX86State* env, uintptr_t pc)
{
    int mode = 2;

    uintptr_t p = (uintptr_t)env->regs[R_EDI];
    size_t len = (uintptr_t)env->regs[R_EDX];
    if (len == 0) {
        return mode;
    }
    if (p == 0) {
        return 0;
    }

    char c = (char)(uintptr_t)env->regs[R_ESI];
    void *res = NULL;
    size_t consumed = 0;
    while (consumed < len) {
        if (p > (target_ulong)-1 - consumed) return 0;
        target_ulong addr = p + consumed;
        size_t chunk = MIN(TARGET_PAGE_SIZE - (addr & ~TARGET_PAGE_MASK),
                            len - consumed);
        if (!prov_range_readable(addr, chunk)) return 0;
        const unsigned char *bytes = g2h(addr);
        res = memchr(bytes, (unsigned char)c, chunk);
        if (res) {
            consumed += (const unsigned char *)res - bytes + 1;
            break;
        }
        consumed += chunk;
    }
    len = consumed;
    if (binradar_memcheck_enabled) {
        provenance_model_check_access(env, (target_ulong)p, len, pc, R_EDI);
    }
    if (!symbolic_mode) return mode;

    bool exprs_allocated = false;
    Expr** exprs = get_expr_addr_span(p, len, &exprs_allocated);
    if (exprs == NULL) {
        return mode;
    }

    int s1_is_not_null = 0;
    if (exprs) {
        for (size_t i = 0; i < len && s1_is_not_null == 0; i++) {
            s1_is_not_null |= exprs[i] != NULL;
        }
    }

    if (!s1_is_not_null) {
        if (exprs_allocated) {
            g_free(exprs);
        }
        return mode;
    }

    Expr* expr = build_expr(exprs, (void*)p, len);
    if (exprs_allocated) {
        g_free(exprs);
    }

    uint16_t offset = res == NULL ? 0 : (((uintptr_t)res) - p) + 1;

    uint64_t v = 0;
    v          = PACK_0(v, offset);
    v          = PACK_1(v, len);
    v          = PACK_2(v, c);

    Expr* e = new_expr();
    e->opkind = MODEL;
    e->op1 = expr;
    SET_EXPR_CONST_OP(e->op2, e->op2_is_const, v);

    add_query_with_model(e, pc, MODEL_MEMCHR, "model_memchr");
    // next_query[0].query   = e;
    // next_query[0].address = pc;
    // next_query[0].model   = MODEL_MEMCHR;
    // next_query++;

    return mode;
}

static inline int model_memcmp(CPUX86State* env, uintptr_t pc)
{
    int mode = 2;
    char* s1 = (char *)(uintptr_t)env->regs[R_EDI];
    char* s2 = (char *)(uintptr_t)env->regs[R_ESI];

    size_t n = (uintptr_t)env->regs[R_EDX];
    if (n == 0) {
        return mode;
    }
    if (s1 == NULL || s2 == NULL) {
        return 0;
    }

    size_t consumed;
    int res;
    if (!prov_compare_scan((target_ulong)s1, (target_ulong)s2, n, true,
                           false, &consumed, &res)) return 0;
    n = consumed;
    /* memcheck-only: validate the read ranges here (access pc = caller). */
    if (binradar_memcheck_enabled) {
        provenance_model_check_access(env, (target_ulong)s1, n, pc, R_EDI);
        provenance_model_check_access(env, (target_ulong)s2, n, pc, R_ESI);
    }

    if (!symbolic_mode) return mode;
    bool s1_exprs_allocated = false, s2_exprs_allocated = false;
    Expr** s1_exprs = get_expr_addr_span((uintptr_t)s1, n,
                                         &s1_exprs_allocated);
    Expr** s2_exprs = get_expr_addr_span((uintptr_t)s2, n,
                                         &s2_exprs_allocated);

    if (s1_exprs == NULL && s2_exprs == NULL) {
        return mode;
    }

    int s1_is_not_null = 0;
    if (s1_exprs) {
        for (size_t i = 0; i < n && s1_is_not_null == 0; i++) {
            s1_is_not_null |= s1_exprs[i] != NULL;
        }
    }

    int s2_is_not_null = 0;
    if (s2_exprs) {
        for (size_t i = 0; i < n && s2_is_not_null == 0; i++) {
            s2_is_not_null |= s2_exprs[i] != NULL;
        }
    }

    if (!s1_is_not_null && !s2_is_not_null) {
        if (s1_exprs_allocated) {
            g_free(s1_exprs);
        }
        if (s2_exprs_allocated) {
            g_free(s2_exprs);
        }
        return mode;
    }

    Expr* s1_expr = build_expr(s1_exprs, s1, n);
    Expr* s2_expr = build_expr(s2_exprs, s2, n);
    if (s1_exprs_allocated) {
        g_free(s1_exprs);
    }
    if (s2_exprs_allocated) {
        g_free(s2_exprs);
    }

    uint64_t v = 0;
    v          = PACK_0(v, res);
    v          = PACK_1(v, n);

    Expr* e = new_expr();
    e->opkind = MODEL;
    e->op1 = s1_expr;
    e->op2 = s2_expr;
    SET_EXPR_CONST_OP(e->op3, e->op3_is_const, v);

    add_query_with_model(e, pc, MODEL_MEMCMP, "model_memcmp");
    // next_query[0].query   = e;
    // next_query[0].address = pc;
    // next_query[0].model   = MODEL_MEMCMP;
    // next_query++;

    return mode;
}

static inline void model_alloc(CPUX86State* env, uintptr_t pc,
                               uintptr_t reg_with_size,
                               target_ulong snapshot_size)
{
    Expr* size_expr = NULL;
    switch (reg_with_size)
    {
        case R_EDI:
            size_expr = s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "rdi"))];
            break;
        case R_ESI:
            size_expr = s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "rsi"))];
            break;
        
        default:
            tcg_abort();
    }
    
    size_t size = (size_t)(uintptr_t)env->regs[reg_with_size];
    symbolic_trace_pending_alloc(size_expr, (target_ulong)size, pc);
    snapshot_trace_pending_allocs(snapshot_size, pc);
    
    if (size_expr == NULL) {
        return;
    }

    Expr* e = new_expr();
    e->opkind = MODEL;
    e->op1 = size_expr;
    SET_EXPR_CONST_OP(e->op2, e->op2_is_const, size);
    
    add_query_with_model(e, pc, MODEL_MALLOC, "model_alloc");
    // next_query[0].query   = e;
    // next_query[0].address = pc;
    // next_query[0].model   = MODEL_MALLOC;
    // next_query++;
}

static inline int model_atoi_like(CPUX86State* env, uintptr_t pc,
                                  MODEL_T model_kind)
{
    int mode = 2;
    const char* s = (const char*)(uintptr_t)env->regs[R_EDI];
    long long result = 0;
    int used_base = 10;

    if (s == NULL) {
        return mode;
    }

    if (model_kind == MODEL_ATOI) {
        result = (long long)atoi(s);
    } else if (model_kind == MODEL_ATOL) {
        result = (long long)atol(s);
    } else {
        result = atoll(s);
    }

    size_t span = model_numeric_span(s, 10, &used_base);
    if (span == 0) {
        span = 1;
    }

    bool exprs_allocated = false;
    Expr** exprs = get_expr_addr_span((uintptr_t)s, span, &exprs_allocated);
    if (!model_has_symbolic_bytes(exprs, span)) {
        if (exprs_allocated) {
            g_free(exprs);
        }
        return mode;
    }

    Expr* input_expr = build_expr(exprs, (void*)s, span);
    if (exprs_allocated) {
        g_free(exprs);
    }
    uint64_t meta = 0;
    meta = PACK_0(meta, span);
    meta = PACK_1(meta, used_base);

    Expr* q = model_build_return_expr(input_expr, (uintptr_t)result, meta);
    add_query_with_model(q, pc, model_kind, "model_atoi_like");
    set_pending_model_return_expr(q);
    return mode;
}

static inline int model_strtol_like(CPUX86State* env, uintptr_t pc,
                                    MODEL_T model_kind)
{
    int mode = 2;
    const char* nptr = (const char*)(uintptr_t)env->regs[R_EDI];
    char** endptr = (char**)(uintptr_t)env->regs[R_ESI];
    int base = (int)(uintptr_t)env->regs[R_EDX];
    char* end_local = NULL;
    uintptr_t concrete_value = 0;
    int used_base = base;

    if (nptr == NULL) {
        return mode;
    }

    if (model_kind == MODEL_STRTOUL) {
        concrete_value = (uintptr_t)strtoul(nptr, &end_local, base);
    } else if (model_kind == MODEL_STRTOULL) {
        concrete_value = (uintptr_t)strtoull(nptr, &end_local, base);
    } else if (model_kind == MODEL_STRTOLL) {
        concrete_value = (uintptr_t)strtoll(nptr, &end_local, base);
    } else {
        concrete_value = (uintptr_t)strtol(nptr, &end_local, base);
    }

    if (endptr != NULL) {
        *endptr = end_local;
        clear_mem((uintptr_t)endptr, sizeof(char*));
    }

    size_t span = model_numeric_span(nptr, base, &used_base);
    if (span == 0) {
        span = 1;
    }

    bool exprs_allocated = false;
    Expr** exprs = get_expr_addr_span((uintptr_t)nptr, span,
                                      &exprs_allocated);
    if (!model_has_symbolic_bytes(exprs, span)) {
        if (exprs_allocated) {
            g_free(exprs);
        }
        return mode;
    }

    Expr* input_expr = build_expr(exprs, (void*)nptr, span);
    if (exprs_allocated) {
        g_free(exprs);
    }
    uint64_t meta = 0;
    uintptr_t end_off = 0;
    if (end_local != NULL) {
        end_off = (uintptr_t)(end_local - nptr);
    }
    meta = PACK_0(meta, span);
    meta = PACK_1(meta, used_base);
    meta = PACK_2(meta, end_off);

    Expr* q = model_build_return_expr(input_expr, concrete_value, meta);
    add_query_with_model(q, pc, model_kind, "model_strtol_like");
    set_pending_model_return_expr(q);
    return mode;
}
