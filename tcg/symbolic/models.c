#include "../../linux-user/provenance.h"

#define MODEL_PARSE_MAX_INPUT 64

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
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "rax"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "rdi"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "rsi"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "rdx"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "rcx"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "r8"))] = 0;
    s_temps[temp_idx(tcg_find_temp_arch_reg(tcg_ctx, "r9"))] = 0;
}

static void add_query_with_model(Expr *q, uintptr_t address, MODEL_T model, const char *msg) {
    next_query->query = q;
    next_query->address = address;
    next_query->model = model;
    if (symbolic_start_code > 0 && address >= symbolic_start_code) {
        printf("[query] [mod-k] [idx %ld] [pc 0x%lx] [msg %s] [syms 0x%lx] [syme 0x%lx]\n", GET_QUERY_IDX(next_query), address, msg, symbolic_start_code, symbolic_end_code);
    } else {
        printf("[query] [mod-u] [idx %ld] [pc 0x%lx] [msg %s]\n", GET_QUERY_IDX(next_query), address, msg);
    }
    next_query++;
}

// clear xmm registers
static inline void clear_xmm_regs(CPUX86State* env)
{
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

static inline int model_strcmp(CPUX86State* env, uintptr_t pc, uintptr_t n)
{
    int mode = 2;
    char* s1 = (char *)(uintptr_t)env->regs[R_EDI];
    char* s2 = (char *)(uintptr_t)env->regs[R_ESI];

    if (s1 == NULL || s2 == NULL) {
        return mode;
    }

    size_t s1_len = n == 0 ? strlen(s1) : strnlen(s1, n);
    size_t s2_len = n == 0 ? strlen(s2) : strnlen(s2, n);
    int res = n == 0 ? strcmp(s1, s2) : strncmp(s1, s2, n);
    size_t len = s1_len > s2_len ? s1_len : s2_len;
    /* memcheck-only: the host string functions read guest memory without
     * interval checks; validate the read ranges here (access pc = caller). */
    if (binradar_memcheck_enabled) {
        provenance_model_check_access(env, (target_ulong)s1, len, pc, R_EDI);
        provenance_model_check_access(env, (target_ulong)s2, len, pc, R_ESI);
    }

    Expr** s1_exprs = get_expr_addr((uintptr_t)s1, len, 0, NULL);
    Expr** s2_exprs = get_expr_addr((uintptr_t)s2, len, 0, NULL);

    if (s1_exprs == NULL && s2_exprs == NULL) {
        return mode;
    }

    int s1_is_not_null = 0;
    if (s1_exprs) {
        for (size_t i = 0; i < len && s1_is_not_null == 0; i++) {
            s1_is_not_null |= s1_exprs[i] != NULL;
        }
    }

    int s2_is_not_null = 0;
    if (s2_exprs) {
        for (size_t i = 0; i < len && s2_is_not_null == 0; i++) {
            s2_is_not_null |= s2_exprs[i] != NULL;
        }
    }

    if (!s1_is_not_null && !s2_is_not_null) {
        return mode;
    }

    Expr* s1_expr = build_expr(s1_exprs, s1, len);
    Expr* s2_expr = build_expr(s2_exprs, s2, len);

    uint64_t v = 0;
    v          = PACK_0(v, res);
    v          = PACK_1(v, s1_len);
    v          = PACK_2(v, s2_len);
    v          = PACK_3(v, n);

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

static inline int model_strlen(CPUX86State* env, uintptr_t pc, uintptr_t n)
{
    int mode = 2;
    char* s1 = (char *)(uintptr_t)env->regs[R_EDI];

    if (s1 == NULL) {
        return mode;
    }

    // printf("n: %lu\n", n);

    size_t s1_len = n == 0 ? strlen(s1) : strnlen(s1, n);
    size_t len = n == 0 || s1_len < n ? s1_len + 1 : s1_len;
    /* memcheck-only: the host string function reads guest memory without
     * interval checks; validate the read range here (access pc = caller). */
    if (binradar_memcheck_enabled) {
        provenance_model_check_access(env, (target_ulong)s1, len, pc, R_EDI);
    }
    // printf("LEN: %lu\n", len);
    Expr** s1_exprs = get_expr_addr((uintptr_t)s1, len, 0, NULL);

    if (s1_exprs == NULL) {
        return mode;
    }

    int s1_is_not_null = 0;
    if (s1_exprs) {
        for (size_t i = 0; i < len && s1_is_not_null == 0; i++) {
            s1_is_not_null |= s1_exprs[i] != NULL;
        }
    }

    if (!s1_is_not_null) {
        return mode;
    }

    Expr* s1_expr = build_expr(s1_exprs, s1, len);

    uint64_t v = 0;
    v          = PACK_0(v, s1_len);
    v          = PACK_1(v, n);

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

static inline int model_memchr(CPUX86State* env, uintptr_t pc)
{
    int mode = 2;

    uintptr_t p = (uintptr_t)env->regs[R_EDI];
    if (p == 0) {
        return mode;
    }

    size_t len = (uintptr_t)env->regs[R_EDX];
    if (len == 0) {
        return mode;
    }

    char c = (char)(uintptr_t)env->regs[R_ESI];
    /* memcheck-only: the host memchr reads guest memory without interval
     * checks; validate the read range here (access pc = caller). */
    if (binradar_memcheck_enabled) {
        provenance_model_check_access(env, (target_ulong)p, len, pc, R_EDI);
    }

    Expr** exprs = get_expr_addr(p, len, 0, NULL);
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
        return mode;
    }

    Expr* expr = build_expr(exprs, (void*)p, len);

    void* res = memchr((void*)p, c, len);
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

    if (s1 == NULL || s2 == NULL) {
        return mode;
    }

    size_t n = (uintptr_t)env->regs[R_EDX];
    if (n == 0) {
        return mode;
    }

    int res = memcmp(s1, s2, n);
    /* memcheck-only: the host memcmp reads guest memory without interval
     * checks; validate the read ranges here (access pc = caller). */
    if (binradar_memcheck_enabled) {
        provenance_model_check_access(env, (target_ulong)s1, n, pc, R_EDI);
        provenance_model_check_access(env, (target_ulong)s2, n, pc, R_ESI);
    }

    Expr** s1_exprs = get_expr_addr((uintptr_t)s1, n, 0, NULL);
    Expr** s2_exprs = get_expr_addr((uintptr_t)s2, n, 0, NULL);

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
        return mode;
    }

    Expr* s1_expr = build_expr(s1_exprs, s1, n);
    Expr* s2_expr = build_expr(s2_exprs, s2, n);

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

static inline void model_alloc(CPUX86State* env, uintptr_t pc, uintptr_t reg_with_size)
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
    snapshot_trace_pending_allocs((target_ulong)size, pc);
    
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

    Expr** exprs = get_expr_addr((uintptr_t)s, span, 0, NULL);
    if (!model_has_symbolic_bytes(exprs, span)) {
        return mode;
    }

    Expr* input_expr = build_expr(exprs, (void*)s, span);
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

    Expr** exprs = get_expr_addr((uintptr_t)nptr, span, 0, NULL);
    if (!model_has_symbolic_bytes(exprs, span)) {
        return mode;
    }

    Expr* input_expr = build_expr(exprs, (void*)nptr, span);
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
