#ifndef BINRADAR_SNAPSHOT_H
#define BINRADAR_SNAPSHOT_H

#include "qemu/osdep.h"
#include "qemu.h"

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

extern bool restoring_to_snapshot;
extern target_ulong binradar_entrypoint;

#define SNAPSHOT_PAGE_SIZE 4096
#define SNAPSHOT_PAGE_MASK ~(SNAPSHOT_PAGE_SIZE - 1)

typedef struct {
    target_ulong addr;
    int perms;
    void *data;
} SnapshotPageInfo;

typedef struct {
    target_ulong access_cache[4];
    int access_cache_idx;
    GHashTable *dirty_pages;
} SnapshotTLS;

typedef struct {
    target_ulong start;
    target_ulong len;
} SnapshotMapping;

typedef struct {
    GHashTable *pages;
    target_ulong start_brk;
    target_ulong start_mmap;
    
    GList *new_mappings;
    
    CPUArchState *cpu_state;
    
    bool is_snapshot_taken;
} SnapshotState;

void snapshot_init(void);
bool snapshot_is_taken(void);
void snapshot_save(CPUArchState *cpu);
void snapshot_restore(CPUArchState *cpu);

void snapshot_access(target_ulong addr, int size);

void snapshot_syscall(uintptr_t syscall_no, uintptr_t syscall_arg0,
                      uintptr_t syscall_arg1, uintptr_t syscall_arg2,
                      uintptr_t syscall_arg3, uintptr_t syscall_arg4,
                      uintptr_t syscall_arg5, uintptr_t syscall_arg6,
                      uintptr_t ret_val);
void snapshot_syscall_munmap(target_ulong addr, target_ulong len);
int snapshot_is_unmap_allowed(target_ulong addr, target_ulong len);

void snapshot_add_mapping(target_ulong addr, target_ulong len);
void snapshot_remove_mapping(target_ulong addr, target_ulong len);

void snapshot_fork_setup(void);
void snapshot_forkserver(CPUState *cpu);

#endif /* BINRADAR_SNAPSHOT_H */
