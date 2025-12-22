#include "snapshot.h"

#include "qemu/rcu.h"

#include <stdio.h>
#include <stdint.h>

#include <sys/mman.h>

#define FORKSRV_FD 198

extern target_ulong target_brk;
bool restoring_to_snapshot;
target_ulong binradar_entrypoint = (target_ulong)-1;

static SnapshotState g_snapshot;
static __thread SnapshotTLS *g_tls_w = NULL;
static __thread SnapshotTLS *g_tls_r = NULL;
static GTree *g_memtree = NULL;
static GArray *pending_allocs = NULL;

static FixedSizeMap g_fixed_size_map;
// static GHashTable *g_pointer_access = NULL;

void pointer_map_init(void) {
    if (g_fixed_size_map.table != NULL) return;
    g_fixed_size_map.max_size = 1024;
    g_fixed_size_map.table = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, g_free);
    g_fixed_size_map.queue = g_queue_new();
}

void fixed_size_map_insert(uintptr_t key, uintptr_t base, uint64_t offset) {
    FixedSizeMap *map = &g_fixed_size_map;
    if (map->table == NULL) pointer_map_init();
    if (g_hash_table_contains(map->table, GUINT_TO_POINTER(key))) {
        g_queue_remove(map->queue, GUINT_TO_POINTER(key));
        g_hash_table_remove(map->table, GUINT_TO_POINTER(key));
    }

    if (g_queue_get_length(map->queue) >= map->max_size) {
        gpointer oldest_key = g_queue_pop_head(map->queue);
        g_hash_table_remove(map->table, oldest_key);
    }

    PointerDecomposition *val = g_new(PointerDecomposition, 1);
    val->base = base;
    val->offset = offset;

    g_hash_table_insert(map->table, GUINT_TO_POINTER(key), val);
    g_queue_push_tail(map->queue, GUINT_TO_POINTER(key));
}

PointerDecomposition* fixed_size_map_lookup(uintptr_t key) {
    FixedSizeMap *map = &g_fixed_size_map;
    if (map->table == NULL) pointer_map_init();
    return (PointerDecomposition*)g_hash_table_lookup(map->table, GUINT_TO_POINTER(key));
}

bool is_valid_address(target_ulong addr) {
    if (g_snapshot.pages == NULL) {
        fprintf(stderr, "ERROR! No valid pages\n");
        return false;
    }
    target_ulong page = addr & SNAPSHOT_PAGE_MASK;
    SnapshotPageInfo *info = g_hash_table_lookup(g_snapshot.pages, &page);
    if (info != NULL) {
        return true;
    }
    return false;
}

// static GHashTable *get_pointer_access_table(void) {
//     if (g_pointer_access == NULL) {
//         g_pointer_access = g_hash_table_new_full(g_int64_hash, g_int64_equal, NULL, g_free);
//     }
//     return g_pointer_access;
// }

// static void access_pointer(target_ulong addr, target_ulong value, bool is_read) {
//     GHashTable *pointer_access = get_pointer_access_table();
//     if (is_read) {
//         fprintf(stderr, "%lx\n", (uintptr_t)pointer_access);
//     }
// }


static GArray *get_pending_allocs(void) {
    if (pending_allocs == NULL) {
        pending_allocs = g_array_new(FALSE, FALSE, sizeof(PendingAlloc));
    }
    return pending_allocs;
}

void snapshot_trace_pending_allocs(target_ulong size, target_ulong pc) {
    GArray *stack = get_pending_allocs();
    PendingAlloc alloc = {size, pc};
    g_array_append_val(stack, alloc);
    fprintf(stderr, "temp alloc size %lx pc %lx\n", size, pc);
}

PendingAlloc snapshot_trace_get_pending_allocs(target_ulong pc) {
    GArray *stack = get_pending_allocs();
    PendingAlloc result = {0, 0};
    if (stack->len == 0) {
        // This should not happen
        return result;
    }
    result = g_array_index(stack, PendingAlloc, stack->len - 1);
    if (result.pc != pc) {
        result = (PendingAlloc){0, 0};
        return result;
    }
    g_array_set_size(stack, stack->len - 1);
    return result;
}


static SnapshotTLS* get_tls_w(void) {
    if (g_tls_w == NULL) {
        g_tls_w = g_malloc0(sizeof(SnapshotTLS));
        g_tls_w->dirty_pages = g_hash_table_new(g_int64_hash, g_int64_equal);
        for(int i=0; i<4; i++) g_tls_w->access_cache[i] = -1;
    }
    return g_tls_w;
}

static SnapshotTLS *get_tls_r(void) {
    if (g_tls_r == NULL) {
        g_tls_r = g_malloc0(sizeof(SnapshotTLS));
        g_tls_r->dirty_pages = g_hash_table_new(g_int64_hash, g_int64_equal);
        for(int i=0; i<4; i++) g_tls_r->access_cache[i] = -1;
    }
    return g_tls_r;
}

gint compare_regions(gconstpointer a, gconstpointer b, gpointer user_data);
gint search_region(gconstpointer key, gconstpointer user_data);

gint compare_regions(gconstpointer a, gconstpointer b, gpointer user_data) {
    const SnapshotMemObject *ra = (const SnapshotMemObject *)a;
    const SnapshotMemObject *rb = (const SnapshotMemObject *)b;
    if (ra->base < rb->base) return -1;
    if (ra->base > rb->base) return 1;
    return 0;
}

gint search_region(gconstpointer key, gconstpointer user_data) {
    const SnapshotMemObject *region = (const SnapshotMemObject *)key;
    const target_ulong addr = *(const target_ulong *)user_data;
    if (addr < region->base) return 1;
    if (addr >= region->base + region->size) return -1;
    return 0;
}

static GTree *get_memtree(void) {
    if (g_memtree == NULL) {
        g_memtree = g_tree_new_full(
            (GCompareDataFunc)compare_regions,
            NULL,
            g_free,
            NULL
        );
    }
    return g_memtree;
}

void snapshot_trace_alloc(target_ulong base, target_ulong size, target_ulong pc) {
    SnapshotMemObject *obj = g_new(SnapshotMemObject, 1);
    obj->base = base;
    obj->size = size;
    obj->pc = pc;
    GTree *memtree = get_memtree();
    g_tree_insert(memtree, obj, obj);
    fprintf(stderr, "[alloc] [done] [base %lx] [size %lx] [pc %lx]\n", base, size, pc);
}

void snapshot_trace_free(target_ulong base, target_ulong pc) {
    GTree *memtree = get_memtree();
    SnapshotMemObject key = {base, 0, 0};
    if (!g_tree_remove(memtree, &key)) {
        fprintf(stderr, "[free] [error] [base %lx] [pc %lx] not exist\n", base, pc);
    } else {
        fprintf(stderr, "[free] [done] [base %lx] [pc %lx]\n", base, pc);
    }
}

bool snapshot_is_taken(void) {
    // return g_snapshot.is_snapshot_taken;
    return true;
}

void snapshot_init(void) {
    memset(&g_snapshot, 0, sizeof(SnapshotState));
    g_snapshot.pages = g_hash_table_new_full(g_int64_hash, g_int64_equal, g_free, g_free);
    g_snapshot.is_snapshot_taken = false;
    // g_snapshot.cpu_state = malloc(sizeof(CPUArchState));
    // memset(g_snapshot.cpu_state, 0, sizeof(CPUArchState));
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
            // memcpy(info->data, host_addr, SNAPSHOT_PAGE_SIZE);

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
    // CPU state
    // if (g_snapshot.cpu_state) {
    //     fprintf(stderr, "[snapshot] [cpu] [at %lx] [size %ld]\n", (uintptr_t)cpu, sizeof(CPUArchState));
    //     memcpy(g_snapshot.cpu_state, cpu, sizeof(CPUArchState));
    // }
    // Memory
    walk_memory_regions(&g_snapshot, walk_memory_cb);

    g_snapshot.start_brk = target_brk;
    g_snapshot.start_mmap = mmap_next_start;
    
    g_snapshot.is_snapshot_taken = true;
    fprintf(stderr, "[snapshot] [result] [brk %llx] [mmap %llx] [pages %d]\n", (long long int)target_brk, (long long int)mmap_next_start, g_hash_table_size(g_snapshot.pages));
}

void snapshot_write_access(SnapshotMemAccess *mem_access) {
    SnapshotTLS *tls = get_tls_w();
    uint64_t addr = mem_access->addr;
    uint64_t size = mem_access->size;
    if (size == sizeof(target_ulong)) {
        target_ulong target;
        memcpy(&target, mem_access->target, sizeof(target_ulong));
        if (is_valid_address(target)) {
            // Trace
        }
    }
    
    target_ulong start = addr & SNAPSHOT_PAGE_MASK;
    target_ulong end = (addr + size - 1) & SNAPSHOT_PAGE_MASK;
    fprintf(stderr, "[snapshot] [waccess] [mem] [addr %lx] [size %ld]\n", addr, size);

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

void snapshot_read_access(SnapshotMemAccess *mem_access) {
    SnapshotTLS *tls = get_tls_r();
    uintptr_t addr = mem_access->addr;
    uintptr_t size = mem_access->size;
    target_ulong start = addr & SNAPSHOT_PAGE_MASK;
    target_ulong end = (addr + size - 1) & SNAPSHOT_PAGE_MASK;
    fprintf(stderr, "[snapshot] [raccess] [mem] [addr %lx] [size %ld]\n", addr, size);

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

// Unused: replaced by fork server
void snapshot_restore(CPUArchState *cpu) {
    // CPU state
    restoring_to_snapshot = true;
    if (g_snapshot.cpu_state) {
        fprintf(stderr, "[snapshot] [restore-cpu]\n");
        memcpy(cpu, g_snapshot.cpu_state, sizeof(CPUArchState));
    }
    
    SnapshotTLS *tls = get_tls_w();
    // mmap
    while (g_snapshot.new_mappings != NULL) {
        SnapshotMapping *map = (SnapshotMapping *)g_snapshot.new_mappings->data;
        // Remove new mmap
        fprintf(stderr, "[snapshot] [restore] [munmap] [addr %lx]\n", map->start);
        target_munmap(map->start, map->len);
        g_free(map);
        g_snapshot.new_mappings = g_list_delete_link(g_snapshot.new_mappings, g_snapshot.new_mappings);
    }

    // brk
    // The heap has shrunk - restore missing pages
    if (target_brk < g_snapshot.start_brk) {
        target_ulong aligned_new_brk = (target_brk + (SNAPSHOT_PAGE_SIZE - 1)) & (~(SNAPSHOT_PAGE_SIZE - 1));
        fprintf(stderr, "[snapshot] [restore] [brk-s] [snap %lx] [new %lx] [aligned %lx] [size %lx]\n", target_brk, g_snapshot.start_brk, aligned_new_brk, g_snapshot.start_brk - aligned_new_brk);
        abi_long brk_ret = do_brk(g_snapshot.start_brk);
        if (brk_ret != g_snapshot.start_brk) {
            fprintf(stderr, "[snapshot] [restore] [brk-s-err] [grow-failed %lx]\n", brk_ret);
        }
    } else if (target_brk > g_snapshot.start_brk) { // Remove new allocations
        fprintf(stderr, "[snapshot] [restore] [brk-l] [snap %lx] [new %lx]\n", target_brk, g_snapshot.start_brk);
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
            fprintf(stderr, "[snapshot] [restore] [dirty] [addr %lx]\n", (uintptr_t)addr);
        } else {
            // void *host_addr = g2h(addr);
            // memset(host_addr, 0, SNAPSHOT_PAGE_SIZE);
            fprintf(stderr, "[snapshot] [restore] [dirty-unknown] [addr %lx]\n", (uintptr_t)addr);
        }
    }

    g_hash_table_remove_all(tls->dirty_pages);
    for(int i=0; i<4; i++) tls->access_cache[i] = -1;
    
    fprintf(stderr, "[snapshot] [restore] [fin]\n");
    fflush(stderr);
}

// Syscall Hook
void snapshot_syscall(uintptr_t syscall_no, uintptr_t syscall_arg0,
                      uintptr_t syscall_arg1, uintptr_t syscall_arg2,
                      uintptr_t syscall_arg3, uintptr_t syscall_arg4,
                      uintptr_t syscall_arg5, uintptr_t syscall_arg6,
                      uintptr_t ret_val) {
    switch (syscall_no) {
    case TARGET_NR_read:
    case TARGET_NR_pread64: // read from file (write to buffer)
        // read(fd, buf, count) -> read count
        if ((long)ret_val > 0) {
            // addr
            SnapshotMemAccess mem_access = {
                .symbolic_addr = false,
                .symbolic_value = false,
                .addr = syscall_arg1,
                .target = {0},
                .ptr = NULL,
                .size = ret_val
            };
            if (ret_val <= 8) {
                void *buf = g2h(syscall_arg1);
                memcpy(mem_access.target, buf, ret_val);
            }
            snapshot_write_access(&mem_access);
        }
        break;
    case TARGET_NR_write:
    case TARGET_NR_pwrite64: // write to file (read from buffer)
        if ((long)ret_val > 0) {
            SnapshotMemAccess mem_access = {
                .symbolic_addr = false,
                .symbolic_value = false,
                .addr = syscall_arg1,
                .target = {0},
                .ptr = NULL,
                .size = ret_val
            };
            if (ret_val <= 8) {
                void *buf = g2h(syscall_arg1);
                memcpy(mem_access.target, buf, ret_val);
            }
            snapshot_read_access(&mem_access);
        }
        break;
    case TARGET_NR_readlinkat: // Read path from symbolic link
        // readlinkat(dirfd, pathname, buf, bufsize)
        // snapshot_write_access(syscall_arg2, syscall_arg3);
#if defined(TARGET_NR_futex)
    case TARGET_NR_futex: // Fast user mutex
        // futex(uaddr, op, val, timeout)
        // snapshot_write_access(syscall_arg0, syscall_arg3);
        break;
#endif
#if defined(TARGET_NR_newfstatat)
    case TARGET_NR_newfstatat: // Return file status as stat
        // newfstatat(dirfd, pathname, statbuf, flags)
        // snapshot_write_access(syscall_arg2, 4096);
        break;
#endif
#if defined(TARGET_NR_fstatat64)
    case TARGET_NR_fstatat64:
        // snapshot_write_access(syscall_arg2, 4096);
        break;
#endif
    case TARGET_NR_statfs:
    case TARGET_NR_fstat:
    case TARGET_NR_fstatfs:
        // fstat(fd, statbuf)
        // snapshot_write_access(syscall_arg1, 4096);
        break;
    case TARGET_NR_getrandom: {
        // getrandom(buf, buflen, flags)
        SnapshotMemAccess mem_access = {
            .symbolic_addr = false,
            .symbolic_value = false,
            .addr = syscall_arg0,
            .target = {0},
            .ptr = NULL,
            .size = syscall_arg1
        };
        if (syscall_arg1 <= 8) {
            void *buf = g2h(syscall_arg0);
            memcpy(mem_access.target, buf, syscall_arg1);
        }
        snapshot_write_access(&mem_access);
        break;
    }
    case TARGET_NR_brk: // heap adjustment
        // brk(new_brk_addr)
        // Handled in snapshot_restore
        fprintf(stderr, "New brk %lx received.\n", syscall_arg0);
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

bool forkserver_installed = false;
unsigned char afl_fork_child;
unsigned int  afl_forksrv_pid;

void snapshot_fork_setup(void) {
    fprintf(stderr, "[forkserver] [setup]\n");
}

static void snapshot_modify_memory(void) {
    
}

void snapshot_forkserver(CPUState *cpu) {
    fprintf(stderr, "[snapshot] [forkserver] [called %d]\n", forkserver_installed);
    if (forkserver_installed) return;
    forkserver_installed = true;
    snapshot_save();
    pid_t child_pid;
    // int   t_fd[2];
    
    unsigned int dropped_rcu = 0;
    while (rcu_reader.depth > 0) {
        rcu_read_unlock();
        dropped_rcu++;
    } 
    
    bool  child_stopped = false;
    uint32_t   was_killed;
    uint32_t version = 0x41464c00;
    uint32_t tmp = version ^ 0xffffffff, status2, status = version;
    uint8_t *msg = (uint8_t *)&status;
    uint8_t *reply = (uint8_t *)&status2;
  
    /* Tell the parent that we're alive. If the parent doesn't want
       to talk, assume that we're not running in forkserver mode. */
  
    if (write(FORKSRV_FD + 1, msg, 4) != 4) {
        fprintf(stderr, "[snapshot] [forkserver] [error] failed to write to %d %d\n", FORKSRV_FD + 1, status);
        _exit(1);
    }
  
    afl_forksrv_pid = getpid();
  
    if (read(FORKSRV_FD, reply, 4) != 4) {
        fprintf(stderr, "[snapshot] [forkserver] [error] fuzzolic not responding to %d\n", FORKSRV_FD); 
        _exit(1);
    }
    if (tmp != status2) {
        fprintf(stderr, "wrong forkserver message from fuzzolic.py");
        _exit(1);
    }

    // send welcome message as final message
    if (write(FORKSRV_FD + 1, msg, 4) != 4) { 
        fprintf(stderr, "[snapshot] [forkserver] [error] failed to send final handshake to %d %d\n", FORKSRV_FD + 1, status);
        _exit(1);
    }
  
  
    // END forkserver handshake
    fprintf(stderr, "[forkserver] [start]\n");
  
    /* All right, let's await orders... */
  
    while (1) {
  
        /* Whoops, parent dead? */
    
        if (read(FORKSRV_FD, &was_killed, 4) != 4) {
            fprintf(stderr, "[forkserver] [error] dead?\n");
            exit(2); 
        }
    
        /* If we stopped the child in persistent mode, but there was a race
            condition and afl-fuzz already issued SIGKILL, write off the old
            process. */
    
        if (child_stopped && was_killed) {
    
            child_stopped = 0;
            if (waitpid(child_pid, (int *)&status, 0) < 0) exit(8);
    
        }
    
        if (!child_stopped) {
    
            /* Establish a channel with child to grab translation commands. We'll
            read from t_fd[0], child will write to TSL_FD. */
    
            // if (pipe(t_fd) || dup2(t_fd[1], TSL_FD) < 0) exit(3);
            // close(t_fd[1]);
    
            child_pid = fork();
            if (child_pid < 0) exit(4);
    
            if (!child_pid) {
                
                /* Child process. Close descriptors and run free. */
                snapshot_modify_memory();
                while (dropped_rcu--) {
                    rcu_read_lock();
                }
                afl_fork_child = 1;
                close(FORKSRV_FD);
                close(FORKSRV_FD + 1);
                // close(t_fd[0]);
                return;
    
            }
    
            /* Parent. */
    
            // close(TSL_FD);
    
        } else {
    
            /* Special handling for persistent mode: if the child is alive but
            currently stopped, simply restart it with SIGCONT. */
            
            kill(child_pid, SIGCONT);
            child_stopped = 0;
    
        }
    
        /* Parent. */
    
        if (write(FORKSRV_FD + 1, &child_pid, 4) != 4) exit(5);
    
        /* Collect translation requests until child dies and closes the pipe. */
    
        // afl_wait_tsl(cpu, t_fd[0]);
    
        /* Get and relay exit status to parent. */
    
        if (waitpid(child_pid, (int *)&status, 0) < 0) exit(6);
    
        /* In persistent mode, the child stops itself with SIGSTOP to indicate
            a successful run. In this case, we want to wake it up without forking
            again. */
    
        if (WIFSTOPPED(status))
            child_stopped = 1;
    
        if (write(FORKSRV_FD + 1, &status, 4) != 4) exit(7);
  
    }

}
