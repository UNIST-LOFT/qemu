#ifndef BINRADAR_SNAPSHOT_H
#define BINRADAR_SNAPSHOT_H

#include "qemu/osdep.h"
#include "qemu.h"

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

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
    GHashTable *pages;
    target_ulong start_brk;
    target_ulong start_mmap;
    
    GList *new_mappings;          
    
    bool is_snapshot_taken;
} SnapshotState;

void snapshot_init(void);
void snapshot_save(void);
void snapshot_restore(void);

void snapshot_access(target_ulong addr, int size);

void snapshot_syscall_mmap(target_ulong addr, target_ulong len, int prot);
void snapshot_syscall_munmap(target_ulong addr, target_ulong len);
int snapshot_is_unmap_allowed(target_ulong addr, target_ulong len);

#endif /* BINRADAR_SNAPSHOT_H */
