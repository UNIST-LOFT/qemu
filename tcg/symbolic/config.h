#ifndef SYMBOLIC_CONFIG_H
#define SYMBOLIC_CONFIG_H

typedef enum {
    NO_INPUT,
    READ_FD_0,
    REG,
    BUFFER,
    FROM_FILE
} SYMBOLIC_INJECT_INPUT_MODE;

typedef struct SymbolicConfig {
    uint64_t                   expr_pool_shm_key;
    uint64_t                   query_shm_key;
#if BRANCH_COVERAGE == FUZZOLIC
    uint64_t                   bitmap_shm_key;
#endif
    uintptr_t                  symbolic_exec_start_addr;
    uintptr_t                  symbolic_exec_stop_addr;
    SYMBOLIC_INJECT_INPUT_MODE symbolic_inject_input_mode;
    const char*                symbolic_exec_reg_name;
    uintptr_t                  symbolic_exec_reg_instr_addr;
    uintptr_t                  symbolic_exec_buffer_addr;
    uintptr_t                  symbolic_exec_buffer_instr_addr;
    const char*                inputfile;
    //
    uintptr_t plt_stub_malloc;
    uintptr_t plt_stub_realloc;
    uintptr_t plt_stub_free;
    uintptr_t plt_stub_printf;
    //
    const char* coverage_tracer;
    const char* coverage_tracer_log_bb;
    const char* coverage_tracer_log_edges;
    int8_t      coverage_tracer_filter_lib;
    //
    int8_t      debug_fuzz_expr;
    /* Runtime NO_EXTERNAL_SOLVER=1 mode: back the expr pool / query queue /
     * bitmap with anonymous MAP_SHARED memory instead of SysV shm and skip the
     * SHM_READY handshake, so the tracer runs without a solver attached.
     * Child writes remain visible after fork; no fixed address is needed
     * because an independent process never attaches to these mappings. */
    int8_t      no_external_solver;
    uint64_t    debug_fuzz_expr_idx;
    uint64_t    debug_fuzz_expr_value;
} SymbolicConfig;

#endif // SYMBOLIC_CONFIG_H