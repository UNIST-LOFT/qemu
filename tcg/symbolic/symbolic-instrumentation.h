#ifndef SYMBOLIC_INSTRUMENTATION_H
#define SYMBOLIC_INSTRUMENTATION_H

#define SYMBOLIC_INSTRUMENTATION
#define SYMBOLIC_CALLSTACK_INSTRUMENTATION 1

extern uint64_t  symbolic_start_code;
extern uint64_t  symbolic_end_code;
extern int       symbolic_force_flush_cache;
// E9Patch relocated call jumps (parsed from E9_RELOCATED_CALL_JUMPS in
// snapshot.c): returns the original call site / return address of the call
// that the jump at `pc` re-implements.
bool is_e9_relocated_call(target_ulong pc, target_ulong *call_site,
                          target_ulong *ret_addr);
extern void qemu_syscall_helper(uintptr_t syscall_no, uintptr_t syscall_arg0,
                                uintptr_t syscall_arg1, uintptr_t syscall_arg2,
                                uintptr_t syscall_arg3, uintptr_t syscall_arg4,
                                uintptr_t syscall_arg5, uintptr_t syscall_arg6,
                                uintptr_t ret_val);
void symbolic_clear_mem(uintptr_t addr, uintptr_t size);
void load_image(char* name, uintptr_t addr);
extern int is_symbolic_model(uintptr_t pc, CPUArchState *cpu);

#include "syscall_nr.h"

#endif // SYMBOLIC_INSTRUMENTATION_H