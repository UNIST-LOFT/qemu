#ifndef __BINRADAR_TRACE_H__
#define __BINRADAR_TRACE_H__

#include "qemuafl/common.h"

void binradar_trace_init_time(void);
void binradar_trace_set_input(const char *path);
void binradar_trace_set_patch_loc(const char *value);
void binradar_trace_set_patch_func_entry(const char *value);
void binradar_trace_set_e9_relocated_call(const char *value);
void binradar_trace_set_asan(const char *mode);
void binradar_trace_ignore_arg(const char *value);
void binradar_trace_enable_basic_blocks(const char *unused);

int binradar_trace_is_enabled(void);
int binradar_trace_symbols_enabled(void);
int binradar_trace_trace_basic_blocks(void);
int binradar_trace_qasan_requested(void);
int binradar_trace_should_hook_pc(target_ulong pc);
int binradar_trace_e9_relocated_call_info(target_ulong pc,
                                          target_ulong *call_site,
                                          target_ulong *ret_addr);
int binradar_trace_should_drop_separator(int target_index, const char *arg);
char *binradar_trace_rewrite_arg(const char *arg);
int binradar_trace_suppress_write_fd(int fd);

void binradar_trace_after_load(target_ulong entry, target_ulong start_code,
                               target_ulong end_code, const char *binary);
/* ELF evidence is collected once at load time, never from guest memory. */
void binradar_trace_load_elf(int fd, target_ulong load_bias);
void binradar_trace_add_function(target_ulong entry, target_ulong size);
void binradar_trace_add_unwind_function(target_ulong entry, target_ulong size);
void binradar_trace_sort_functions(void);
target_ulong binradar_trace_tail_candidate(target_ulong pc, target_ulong entry);
void binradar_trace_tail(target_ulong source, target_ulong entry, target_ulong sp);
void binradar_trace_start(target_ulong pc);
void binradar_trace_record_bb(target_ulong pc);
void binradar_trace_insn_hit(target_ulong pc);
void binradar_trace_call(target_ulong pc, target_ulong return_addr,
                         target_ulong entry, target_ulong stack_addr);
void binradar_trace_relocated_call(target_ulong entry, target_ulong call_site,
                                   target_ulong ret_addr, target_ulong stack_addr);
void binradar_trace_ret(target_ulong pc, target_ulong return_addr);

void binradar_trace_post_syscall(void *cpu_env, int num, target_long ret,
                                 target_long arg1, target_long arg2,
                                 target_long arg3, target_long arg4,
                                 target_long arg5, target_long arg6);
void binradar_trace_report_signal(void *cpu_env, int sig);
void binradar_trace_report_qasan_crash(target_ulong pc, target_ulong fault_addr,
                                       int sig);
void binradar_trace_report_exit(void *cpu_env, int code);

#endif
