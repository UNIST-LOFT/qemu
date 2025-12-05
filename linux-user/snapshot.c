#include "snapshot.h"

#include <stdio.h>
#include <stdint.h>

#include <sys/mman.h>

extern target_ulong target_brk;

static SnapshotState g_snapshot;
static __thread SnapshotTLS *g_tls = NULL;

static SnapshotTLS* get_tls(void) {
    if (g_tls == NULL) {
        g_tls = g_malloc0(sizeof(SnapshotTLS));
        g_tls->dirty_pages = g_hash_table_new(g_int64_hash, g_int64_equal);
        for(int i=0; i<4; i++) g_tls->access_cache[i] = -1;
    }
    return g_tls;
}

bool snapshot_is_taken(void) {
    return g_snapshot.is_snapshot_taken;
}

void snapshot_init(void) {
    memset(&g_snapshot, 0, sizeof(SnapshotState));
    g_snapshot.pages = g_hash_table_new_full(g_int64_hash, g_int64_equal, NULL, g_free);
    g_snapshot.is_snapshot_taken = false;
}

static int walk_memory_cb(void *priv, target_ulong start, target_ulong end,
                          unsigned long flags) {
    if (flags & PAGE_READ) {
        target_ulong addr;
        for (addr = start; addr < end; addr += SNAPSHOT_PAGE_SIZE) {
            SnapshotPageInfo *info = g_malloc0(sizeof(SnapshotPageInfo));
            info->addr = addr;
            info->perms = flags;
            info->data = g_malloc(SNAPSHOT_PAGE_SIZE);
            
            void *host_addr = g2h(addr);
            memcpy(info->data, host_addr, SNAPSHOT_PAGE_SIZE);

            target_ulong *key = g_malloc(sizeof(target_ulong));
            *key = addr;
            g_hash_table_insert(g_snapshot.pages, key, info);
            fprintf(stderr, "[snapshot] [memwalk] [addr %lx] [perms %ld] [host %lx]\n", (uint64_t)addr, flags, (uint64_t)host_addr);
        }
    }
    return 0;
}

void snapshot_save(void) {
    if (g_snapshot.pages == NULL) snapshot_init();
    if (g_snapshot.is_snapshot_taken) return;
    fprintf(stderr, "[snapshot] [mem] [start]\n");
    walk_memory_regions(&g_snapshot, walk_memory_cb);

    g_snapshot.start_brk = target_brk;
    g_snapshot.start_mmap = mmap_next_start;
    
    g_snapshot.is_snapshot_taken = true;
    fprintf(stderr, "[snapshot] [result] [brk %llx] [mmap %llx] [pages %d]\n", (long long int)target_brk, (long long int)mmap_next_start, g_hash_table_size(g_snapshot.pages));
}

void snapshot_access(target_ulong addr, int size) {
    SnapshotTLS *tls = get_tls();
    target_ulong start = addr & SNAPSHOT_PAGE_MASK;
    target_ulong end = (addr + size - 1) & SNAPSHOT_PAGE_MASK;
    fprintf(stderr, "[snapshot] [access] [mem] [addr %lx] [size %d]\n", addr, size);

    for (target_ulong page = start; page <= end; page += SNAPSHOT_PAGE_SIZE) {
        bool cached = false;
        for (int i = 0; i < 4; i++) {
            if (tls->access_cache[i] == page) {
                cached = true;
                break;
            }
        }
        if (cached) continue;

        tls->access_cache[tls->access_cache_idx] = page;
        tls->access_cache_idx = (tls->access_cache_idx + 1) % 4;
        
        if (!g_hash_table_contains(tls->dirty_pages, &page)) {
            target_ulong *key = g_malloc(sizeof(target_ulong));
            *key = page;
            g_hash_table_add(tls->dirty_pages, key);
        }
    }
}

void snapshot_restore(void) {
    SnapshotTLS *tls = get_tls();
    // mmap
    while (g_snapshot.new_mappings != NULL) {
        SnapshotMapping *map = (SnapshotMapping *)g_snapshot.new_mappings->data;
        // Remove new mmap
        target_munmap(map->start, map->len);
        g_free(map);
        g_snapshot.new_mappings = g_list_delete_link(g_snapshot.new_mappings, g_snapshot.new_mappings);
    }

    // brk
    // The heap has shrunk - restore missing pages
    if (target_brk < g_snapshot.start_brk) {
        target_ulong aligned_new_brk = (target_brk + (SNAPSHOT_PAGE_SIZE - 1)) & (!(SNAPSHOT_PAGE_SIZE - 1));
        fprintf(stderr, "[snapshot] [restore] [brk-s] [snap %lx] [new %lx] [aligned %lx] [size %lx]\n", target_brk, g_snapshot.start_brk, aligned_new_brk, g_snapshot.start_brk - aligned_new_brk);
        abi_long brk_ret = do_brk(g_snapshot.start_brk);
        if (brk_ret != g_snapshot.start_brk) {
            fprintf(stderr, "[snapshot] [restore] [brk-s-err] [grow-failed %lx]\n", brk_ret);
        }
    } else if (target_brk > g_snapshot.start_brk) { // Remove new allocations
        
    }

    // 3. Dirty Page
    GHashTableIter iter;
    gpointer key, value;
    g_hash_table_iter_init(&iter, tls->dirty_pages);

    while (g_hash_table_iter_next(&iter, &key, &value)) {
        target_ulong addr = *(target_ulong*)key;
        
        SnapshotPageInfo *info = g_hash_table_lookup(g_snapshot.pages, &addr);
        if (info) {
            // memcpy with original data
            void *host_addr = g2h(addr);
            
            // mprotect(host_addr, SNAPSHOT_PAGE_SIZE, PROT_READ | PROT_WRITE); 
            memcpy(host_addr, info->data, SNAPSHOT_PAGE_SIZE);
        } else {
            void *host_addr = g2h(addr);
            memset(host_addr, 0, SNAPSHOT_PAGE_SIZE);
        }
    }

    g_hash_table_remove_all(tls->dirty_pages);
    for(int i=0; i<4; i++) tls->access_cache[i] = -1;
}

// Syscall Hook
void snapshot_syscall(uintptr_t syscall_no, uintptr_t syscall_arg0,
                      uintptr_t syscall_arg1, uintptr_t syscall_arg2,
                      uintptr_t syscall_arg3, uintptr_t syscall_arg4,
                      uintptr_t syscall_arg5, uintptr_t syscall_arg6,
                      uintptr_t ret_val) {
    switch (syscall_no) {
    case TARGET_NR_read:
    case TARGET_NR_pread64: // read from file
        // read(fd, buf, count) -> read count
        if ((long)ret_val > 0) {
            // addr
            snapshot_access(syscall_arg1, ret_val);
        }
        break;
    case TARGET_NR_readlinkat: // Read path from symbolic link
        // readlinkat(dirfd, pathname, buf, bufsize)
        snapshot_access(syscall_arg2, syscall_arg3);
#if defined(TARGET_NR_futex)
    case TARGET_NR_futex: // Fast user mutex
        // futex(uaddr, op, val, timeout)
        snapshot_access(syscall_arg0, syscall_arg3);
        break;
#endif
#if defined(TARGET_NR_newfstatat)
    case TARGET_NR_newfstatat: // Return file status as stat
        // newfstatat(dirfd, pathname, statbuf, flags)
        snapshot_access(syscall_arg2, 4096);
        break;
#endif
#if defined(TARGET_NR_fstatat64)
    case TARGET_NR_fstatat64:
        snapshot_access(syscall_arg2, 4096);
        break;
#endif
    case TARGET_NR_statfs:
    case TARGET_NR_fstat:
    case TARGET_NR_fstatfs:
        // fstat(fd, statbuf)
        snapshot_access(syscall_arg1, 4096);
        break;
    case TARGET_NR_getrandom:
        // getrandom(buf, buflen, flags)
        snapshot_access(syscall_arg0, syscall_arg1);
        break;
    case TARGET_NR_brk: // heap adjustment
        // brk(new_brk_addr)
        // Handled in snapshot_restore
        fprintf(stderr, "New brk %lx received.", syscall_arg0);
        break;
    // System call that changes heap shape:
    case TARGET_NR_mmap: // Memory map to file
        // mmap(addr, size, prot, flags, fd, offset) -> mapped addr
        snapshot_add_mapping(ret_val, syscall_arg1);
        break;
    case TARGET_NR_mremap: // memory remap
        // mremap(old_addr, old_size, new_size, flags, new_addr) -> new addr
        snapshot_remove_mapping(syscall_arg0, syscall_arg1);
        snapshot_add_mapping(ret_val, syscall_arg2);
        break;
    case TARGET_NR_munmap: // unmap
        // munmap(addr, length)
        snapshot_remove_mapping(syscall_arg0, syscall_arg1);
        break;
    case TARGET_NR_mprotect: // permission
        // mprotect(start, len, prot)
        // BINRADAR TODO: implement
        break;
    default:
        break;
    }
}

// Syscall Hook: munmap (linux-user/syscall.c do_syscall1())
// Do not unmap if any page in the range is in the snapshot
int snapshot_is_unmap_allowed(target_ulong addr, target_ulong len) {
    target_ulong end = addr + len;
    for (target_ulong p = addr; p < end; p += SNAPSHOT_PAGE_SIZE) {
        if (g_hash_table_contains(g_snapshot.pages, &p)) {
            return 0; // False
        }
    }
    return 1; // True
}


void snapshot_add_mapping(target_ulong addr, target_ulong len) {
    if (addr == -1) return;
    SnapshotMapping *map = g_malloc(sizeof(SnapshotMapping));
    map->start = addr;
    map->len = len;
    g_snapshot.new_mappings = g_list_prepend(g_snapshot.new_mappings, map);
    fprintf(stderr, "[snapshot] [mmap] [add] [addr %lx] [len %ld]\n", addr, len);
}

void snapshot_remove_mapping(target_ulong addr, target_ulong len) {
    for (GList *l = g_snapshot.new_mappings; l != NULL; l = l->next) {
        SnapshotMapping *map = (SnapshotMapping *)l->data;
        g_free(map);
        fprintf(stderr, "[snapshot] [munmap] [remove] [addr %lx]\n", addr);
        return;
    }
}
