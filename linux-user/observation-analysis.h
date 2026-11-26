#ifndef BINRADAR_OBSERVATION_ANALYSIS_H
#define BINRADAR_OBSERVATION_ANALYSIS_H

#include "qemu.h"

struct TCGContext;
extern bool observation_analysis_enabled;
void observation_analysis_init(void);
void observation_analysis_image(target_ulong bias, target_ulong code,
                                target_ulong code_end, target_ulong data,
                                target_ulong data_end);
void observation_analysis_instrument(struct TCGContext *s);
void observation_analysis_alloc(target_ulong base, target_ulong size,
                                target_ulong pc, uint64_t id, uint32_t gen,
                                int producer);
void observation_analysis_free(target_ulong base);
void observation_analysis_clobber(void);
void observation_analysis_return_pointer(void);
void observation_analysis_model(bool active, bool supported);
void observation_analysis_allocator(CPUArchState *env, int kind,
                                    target_ulong old_base);
void observation_analysis_overwrite(CPUArchState *env, target_ulong addr,
                                    target_ulong size, int cls);
void observation_analysis_copy(CPUArchState *env, target_ulong src,
                               target_ulong dst, target_ulong size);
void observation_analysis_store(target_ulong addr, target_ulong size);
void observation_analysis_unsupported(const char *reason);
void observation_analysis_signal(CPUArchState *env, int sig,
                                 target_ulong addr);
void observation_analysis_finish(CPUArchState *env);
void observation_analysis_finding(void);
void observation_analysis_syscall_return(void);
void observation_analysis_read(CPUArchState *env, target_ulong addr,
                               target_ulong size);
#endif
