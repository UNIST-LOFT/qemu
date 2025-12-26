#include "snapshot.h"

#include "qemu/rcu.h"

#include <stdio.h>
#include <stdint.h>

#define SNAPSHOT_DEBUG

#ifdef SNAPSHOT_DEBUG
#include <execinfo.h>
#include <signal.h>
#include <unistd.h>

#define SNAPSHOT_BT_DEPTH 64
#endif

#include <sys/mman.h>

#define FORKSRV_FD 198

extern target_ulong target_brk;
bool restoring_to_snapshot;
target_ulong binradar_entrypoint = (target_ulong)-1;

bool forkserver_installed = false;
unsigned char afl_fork_child;
unsigned int  afl_forksrv_pid;

static SnapshotState g_snapshot;
static GTree *g_memtree = NULL;
static GArray *pending_allocs = NULL;

typedef struct {
    uintptr_t addr;
    uintptr_t size;
    uint8_t target[8];
} SingleModification;

typedef struct {
    GQueue *modifications;
    GArray *current;
    GArray *done;
} ModificationManager;

typedef struct {
    int size;
    uintptr_t addr;
    uint64_t access_id;
} PrimitiveAccess;

typedef struct {
    uintptr_t addr;
    uintptr_t target;
    uint64_t access_id;
} PointerAccess;

typedef struct {
    uint32_t prim_idx;
    uint32_t ptr_idx;
    uint64_t prim_access_cnt;
    uint64_t ptr_access_cnt;
    PrimitiveAccess primitives[MAX_PRIMITIVE_ACCESS];
    PointerAccess pointers[MAX_POINTER_ACCESS];
} SharedTraceData;

static SharedTraceData *shared_trace_data = NULL;

static OrderedMap *g_read_access_tainted_primitives = NULL;
static OrderedMap *g_read_access_pointers = NULL;

static ModificationManager *mod_manager = NULL;

OrderedMap *ordered_map_init(int max_size) {
    OrderedMap *map = g_new(OrderedMap, 1);
    map->max_size = max_size;
    map->table = g_hash_table_new_full(g_direct_hash, g_direct_equal, NULL, g_free);
    map->queue = g_queue_new();
    return map;
}

OrderedMapEntry *ordered_map_insert(OrderedMap *map, uintptr_t key, void *data) {
    OrderedMapEntry *existing = g_hash_table_lookup(map->table, GUINT_TO_POINTER(key));
    int old_index = -1;
    if (existing != NULL) {
        old_index = existing->shared_index;
        g_queue_delete_link(map->queue, existing->node);
        g_hash_table_remove(map->table, GUINT_TO_POINTER(key));
    }

    if (map->max_size > 0 && g_queue_get_length(map->queue) >= map->max_size) {
        OrderedMapEntry *oldest_entry = (OrderedMapEntry *)g_queue_pop_head(map->queue);
        if (oldest_entry != NULL) {
            old_index = oldest_entry->shared_index;
            uintptr_t old_key = oldest_entry->key;
            g_hash_table_remove(map->table, GUINT_TO_POINTER(old_key));
        }
    }

    OrderedMapEntry *entry = g_new(OrderedMapEntry, 1);
    memset(entry, 0, sizeof(OrderedMapEntry));
    entry->key = key;
    entry->data = data;
    entry->shared_index = old_index;

    g_queue_push_tail(map->queue, entry);
    entry->node = map->queue->tail;
    g_hash_table_insert(map->table, GUINT_TO_POINTER(key), entry);
    return entry;
}

OrderedMapEntry* ordered_map_lookup(OrderedMap *map, uintptr_t key) {
    OrderedMapEntry *entry = (OrderedMapEntry *)g_hash_table_lookup(map->table, GUINT_TO_POINTER(key));
    return entry;
}

static void add_read_access_pointer(uintptr_t addr, uintptr_t target) {
    if (shared_trace_data == NULL) return;
    if (g_read_access_pointers == NULL) g_read_access_pointers = ordered_map_init(MAX_POINTER_ACCESS);
    OrderedMapEntry *entry = ordered_map_insert(g_read_access_pointers, addr, NULL);
    PointerAccess *ptr = NULL;
    if (entry->shared_index < 0) {
        int new_index = __atomic_fetch_add(&shared_trace_data->ptr_idx, 1, __ATOMIC_RELAXED);
        entry->shared_index = new_index;
        if (new_index < MAX_POINTER_ACCESS) {
            ptr = &shared_trace_data->pointers[new_index];
        }
    } else if (entry->shared_index < MAX_POINTER_ACCESS) {
        ptr = &shared_trace_data->pointers[entry->shared_index];
    }
    if (ptr == NULL) {
        fprintf(stderr, "[rpo] ptr shared_index error!!! %d\n", entry->shared_index);
        exit(1);
    }
    ptr->addr = addr;
    ptr->target = target;
    ptr->access_id = __atomic_fetch_add(&shared_trace_data->ptr_access_cnt, 1, __ATOMIC_RELAXED);
    entry->data = ptr;
    fprintf(stderr, "[rpo] [addr %lx] [target %lx] [index %d] [id %ld]\n", addr, target, entry->shared_index, ptr->access_id);
}

static void add_read_access_primitive(uintptr_t addr, int size) {
    if (shared_trace_data == NULL) return;
    if (g_read_access_tainted_primitives == NULL) g_read_access_tainted_primitives = ordered_map_init(MAX_PRIMITIVE_ACCESS);
    PrimitiveAccess *prim = NULL;
    OrderedMapEntry *entry = ordered_map_insert(g_read_access_tainted_primitives, addr, NULL);
    if (entry->shared_index < 0) {
        int new_index = __atomic_fetch_add(&shared_trace_data->prim_idx, 1, __ATOMIC_RELAXED);
        entry->shared_index = new_index;
        if (new_index < MAX_PRIMITIVE_ACCESS) {
            prim = &shared_trace_data->primitives[new_index];
        }
    } else if (entry->shared_index < MAX_PRIMITIVE_ACCESS) {
        prim = &shared_trace_data->primitives[entry->shared_index];
    }
    if (prim == NULL) {
        fprintf(stderr, "[rpo] prim shared_index error!!! %d\n", entry->shared_index);
        exit(1);
    }
    prim->addr = addr;
    prim->size = size;
    prim->access_id = __atomic_fetch_add(&shared_trace_data->prim_access_cnt, 1, __ATOMIC_RELAXED);
    entry->data = prim;
    fprintf(stderr, "[rpi] [addr %lx] [size %d] [index %d] [id %ld]\n", addr, size, entry->shared_index, prim->access_id);
}

bool is_valid_address(target_ulong addr) {
    if (g_snapshot.pages == NULL) {
        fprintf(stderr, "ERROR! No valid pages\n");
        return false;
    }
    target_ulong page = addr & SNAPSHOT_PAGE_MASK;
    SnapshotPageInfo *info = g_hash_table_lookup(g_snapshot.pages, &page);
    if (info != NULL) {
        // Valid only if it has write permission
        return (info->perms & PAGE_WRITE) != 0;
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
    size_t shm_size = sizeof(SharedTraceData);
    shared_trace_data = mmap(NULL, shm_size, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (shared_trace_data == MAP_FAILED) {
        perror("mmap shared memory failed");
        exit(1);
    }
    memset(shared_trace_data, 0, shm_size);
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
    if (!forkserver_installed) return;
    uint64_t addr = mem_access->addr;
    uint64_t size = mem_access->size;
    if (size == sizeof(target_ulong)) {
        target_ulong target;
        memcpy(&target, mem_access->target, sizeof(target_ulong));
        if (is_valid_address(target)) {
            // Trace?
        }
    }
    // target_ulong start = addr & SNAPSHOT_PAGE_MASK;
    // target_ulong end = (addr + size - 1) & SNAPSHOT_PAGE_MASK;
    fprintf(stderr, "[snapshot] [waccess] [mem] [addr %lx] [size %ld]\n", addr, size);
}

void snapshot_read_access(SnapshotMemAccess *mem_access) {
    if (!forkserver_installed) return;
    uintptr_t addr = mem_access->addr;
    uintptr_t size = mem_access->size;
    // target_ulong start = addr & SNAPSHOT_PAGE_MASK;
    // target_ulong end = (addr + size - 1) & SNAPSHOT_PAGE_MASK;
    bool is_value_pointer = false;
    if (size == sizeof(target_ulong)) {
        target_ulong target;
        memcpy(&target, mem_access->target, sizeof(target_ulong));
        if (is_valid_address(target)) {
            // Add to pointer
            add_read_access_pointer(addr, target);
            is_value_pointer = true;
        }
    }
    if (!is_value_pointer) {
        if (mem_access->symbolic_value) {
            // Tainted value
            add_read_access_primitive(addr, size);
        }
    }
    fprintf(stderr, "[snapshot] [raccess] [mem] [addr %lx] [size %ld]\n", addr, size);
}

// Unused: replaced by fork server
// void snapshot_restore(CPUArchState *cpu) {
//     // CPU state
//     restoring_to_snapshot = true;
//     if (g_snapshot.cpu_state) {
//         fprintf(stderr, "[snapshot] [restore-cpu]\n");
//         memcpy(cpu, g_snapshot.cpu_state, sizeof(CPUArchState));
//     }
    
//     SnapshotTLS *tls = get_tls_w();
//     // mmap
//     while (g_snapshot.new_mappings != NULL) {
//         SnapshotMapping *map = (SnapshotMapping *)g_snapshot.new_mappings->data;
//         // Remove new mmap
//         fprintf(stderr, "[snapshot] [restore] [munmap] [addr %lx]\n", map->start);
//         target_munmap(map->start, map->len);
//         g_free(map);
//         g_snapshot.new_mappings = g_list_delete_link(g_snapshot.new_mappings, g_snapshot.new_mappings);
//     }

//     // brk
//     // The heap has shrunk - restore missing pages
//     if (target_brk < g_snapshot.start_brk) {
//         target_ulong aligned_new_brk = (target_brk + (SNAPSHOT_PAGE_SIZE - 1)) & (~(SNAPSHOT_PAGE_SIZE - 1));
//         fprintf(stderr, "[snapshot] [restore] [brk-s] [snap %lx] [new %lx] [aligned %lx] [size %lx]\n", target_brk, g_snapshot.start_brk, aligned_new_brk, g_snapshot.start_brk - aligned_new_brk);
//         abi_long brk_ret = do_brk(g_snapshot.start_brk);
//         if (brk_ret != g_snapshot.start_brk) {
//             fprintf(stderr, "[snapshot] [restore] [brk-s-err] [grow-failed %lx]\n", brk_ret);
//         }
//     } else if (target_brk > g_snapshot.start_brk) { // Remove new allocations
//         fprintf(stderr, "[snapshot] [restore] [brk-l] [snap %lx] [new %lx]\n", target_brk, g_snapshot.start_brk);
//     }

//     // 3. Dirty Page
//     GHashTableIter iter;
//     gpointer key, value;
//     g_hash_table_iter_init(&iter, tls->dirty_pages);

//     while (g_hash_table_iter_next(&iter, &key, &value)) {
//         target_ulong addr = *(target_ulong*)key;
        
//         SnapshotPageInfo *info = g_hash_table_lookup(g_snapshot.pages, &addr);
//         if (info) {
//             // memcpy with original data
//             void *host_addr = g2h(addr);
            
//             // mprotect(host_addr, SNAPSHOT_PAGE_SIZE, PROT_READ | PROT_WRITE); 
//             memcpy(host_addr, info->data, SNAPSHOT_PAGE_SIZE);
//             fprintf(stderr, "[snapshot] [restore] [dirty] [addr %lx]\n", (uintptr_t)addr);
//         } else {
//             // void *host_addr = g2h(addr);
//             // memset(host_addr, 0, SNAPSHOT_PAGE_SIZE);
//             fprintf(stderr, "[snapshot] [restore] [dirty-unknown] [addr %lx]\n", (uintptr_t)addr);
//         }
//     }

//     g_hash_table_remove_all(tls->dirty_pages);
//     for(int i=0; i<4; i++) tls->access_cache[i] = -1;
    
//     fprintf(stderr, "[snapshot] [restore] [fin]\n");
//     fflush(stderr);
// }

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
        // snapshot_remove_mapping(syscall_arg0, syscall_arg1);
        snapshot_add_mapping(ret_val, syscall_arg2);
        break;
    case TARGET_NR_munmap: // unmap
        // munmap(addr, length)
        // snapshot_remove_mapping(syscall_arg0, syscall_arg1);
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
    return 1;
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

void snapshot_fork_setup(void) {
    fprintf(stderr, "[forkserver] [setup]\n");
}

// Modify guest program's state base on mod_manager (check analyze_collected_data)
// Called after fork to keep clean initial state
static void snapshot_modify_memory(void) {
    if (mod_manager == NULL) {
        // Initial run: no modification
        return;
    }
    // Select one from modifications
    GArray *mods = mod_manager->current;
    if (mods == NULL) {
        fprintf(stderr, "ERROR: empty modification\n");
        exit(1);
    }
    for (int i = 0; i < mods->len; i++) {
        SingleModification mod = g_array_index(mods, SingleModification, i);
        void *target_addr_h = g2h(mod.addr);
        memcpy(target_addr_h, mod.target, mod.size);
        fprintf(stderr, "[mod] [addr %lx] [size %ld] [total %d]\n", mod.addr, mod.size, g_queue_get_length(mod_manager->modifications));
    }
}

#ifdef SNAPSHOT_DEBUG
static void snapshot_sig_handler(int sig, siginfo_t *si, void *ctx) {
    void *frames[SNAPSHOT_BT_DEPTH];
    int n = backtrace(frames, SNAPSHOT_BT_DEPTH);
    dprintf(STDERR_FILENO, "[forkserver-child] fata signal %d (%s) addr=%p\n", sig, strsignal(sig), si ? si->si_addr : NULL);
    backtrace_symbols_fd(frames, n, STDERR_FILENO);
    _exit(128 + sig);
}

static void snapshot_install_crash_handler(void) {
    struct sigaction sa = {
        .sa_sigaction = snapshot_sig_handler,
        .sa_flags = SA_SIGINFO | SA_RESETHAND
    };
    sigemptyset(&sa.sa_mask);
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);
    sigaction(SIGABRT, &sa, NULL);
}
#endif

static int compare_prim_id_desc(const void *a, const void *b) {
    const PrimitiveAccess *pa = (const PrimitiveAccess *)a;
    const PrimitiveAccess *pb = (const PrimitiveAccess *)b;
    
    if (pa->access_id > pb->access_id) return -1;
    if (pa->access_id < pb->access_id) return 1;
    return 0;
}

static int compare_ptr_id_desc(const void *a, const void *b) {
    const PointerAccess *pa = (const PointerAccess *)a;
    const PointerAccess *pb = (const PointerAccess *)b;
    
    if (pa->access_id > pb->access_id) return -1;
    if (pa->access_id < pb->access_id) return 1;
    return 0;
}

static void flip_bits(uint8_t *target, int size) {
    for (int i = 0; i < size; i++) {
        target[i] = ~target[i];
    }
}

// Called after child execution
static void analyze_collected_data(void) {
    if (shared_trace_data == NULL) {
        fprintf(stderr, "Snapshot init error: shared_trace_data is null\n");
        exit(1);
    }
    // Analyze shared_trace_data
    // First run: collect all data
    if (mod_manager == NULL) {
        mod_manager = g_new(ModificationManager, 1);
        mod_manager->modifications = g_queue_new();
        mod_manager->done = g_array_new(FALSE, FALSE, sizeof(GArray *));
        mod_manager->current = NULL;
        // 1. Sort by access_id
        qsort(shared_trace_data->primitives, shared_trace_data->prim_idx, sizeof(PrimitiveAccess), compare_prim_id_desc);
        qsort(shared_trace_data->pointers, shared_trace_data->ptr_idx, sizeof(PointerAccess), compare_ptr_id_desc);
        // 2.  Update mod_manager
        for (int i = 0; i < shared_trace_data->prim_idx; i++) {
            PrimitiveAccess *prim = &shared_trace_data->primitives[i];
            fprintf(stderr, "[analyze] [primitive] [index %d] [addr %lx] [size %d] [id %ld]\n", i, prim->addr, prim->size, prim->access_id);
            SingleModification mod = {
                .addr = prim->addr,
                .size = prim->size,
                .target = {0}
            };
            // Get actual value
            if (prim->size <= 8) {
                void *ptr_h = g2h(prim->addr);
                memcpy(mod.target, ptr_h, prim->size);
            }
            // Set to 0, Set to 1, bitflip
            // TODO: better modification methods
            // TODO: multi loc modification
            switch (mod.size) {
                case 1: {
                    uint8_t val = mod.target[0];
                    if (val != 0) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        mod.target[0] = 0;
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    if (val != 1) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        mod.target[0] = 1;
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                    flip_bits(mod.target, mod.size);
                    g_array_append_val(arr, mod);
                    g_queue_push_tail(mod_manager->modifications, arr);
                    break;
                }
                case 2: {
                    uint16_t val;
                    memcpy(&val, mod.target, 2);
                    if (val != 0) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        memset(mod.target, 0, 2);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    if (val != 1) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        uint16_t one = 1;
                        memcpy(mod.target, &one, 2);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                    flip_bits(mod.target, mod.size);
                    g_array_append_val(arr, mod);
                    g_queue_push_tail(mod_manager->modifications, arr);
                    break;
                }
                case 4: {
                    uint32_t val;
                    memcpy(&val, mod.target, 4);
                    if (val != 0) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        memset(mod.target, 0, 4);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    if (val != 1) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        uint32_t one = 1;
                        memcpy(mod.target, &one, 4);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                    flip_bits(mod.target, mod.size);
                    g_array_append_val(arr, mod);
                    g_queue_push_tail(mod_manager->modifications, arr);
                    break;
                }
                case 8: {
                    uint64_t val;
                    memcpy(&val, mod.target, 8);
                    if (val != 0) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        memset(mod.target, 0, 8);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    if (val != 1) {
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        uint64_t one = 1;
                        memcpy(mod.target, &one, 8);
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    }
                    GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                    flip_bits(mod.target, mod.size);
                    g_array_append_val(arr, mod);
                    g_queue_push_tail(mod_manager->modifications, arr);
                    break;
                }
                default: {
                    // From real memcpy/memmove (if plt is given) or file write
                    if (mod.size < 8) {
                        flip_bits(mod.target, mod.size);
                        GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                        g_array_append_val(arr, mod);
                        g_queue_push_tail(mod_manager->modifications, arr);
                    } else {
                        // TODO: fuzzing
                    }
                }
            }
        }
        for (int i = 0; i < shared_trace_data->ptr_idx; i++) {
            PointerAccess *ptr = &shared_trace_data->pointers[i];
            fprintf(stderr, "[analyze] [pointer] [index %d] [addr %lx] [target %lx] [id %ld]\n", i, ptr->addr, ptr->target, ptr->access_id);
            SingleModification mod = {
                .addr = ptr->addr,
                .size = sizeof(target_ulong),
                .target = {0}
            };
            // Get actual value
            target_ulong actual_value;
            memcpy(&actual_value, g2h(ptr->addr), sizeof(target_ulong));
            memcpy(mod.target, &actual_value, sizeof(target_ulong));
            // Fix pointer
            if (actual_value != 0) {
                // Set to NULL
                GArray *arr = g_array_new(FALSE, FALSE, sizeof(SingleModification));
                target_ulong null_ptr = 0;
                memcpy(mod.target, &null_ptr, sizeof(target_ulong));
                g_array_append_val(arr, mod);
                g_queue_push_tail(mod_manager->modifications, arr);
            } else {
                // Pointer to new object
                // TODO: recognize null pointer
                // TODO: allocate new page with mmap, cache it and reuse it
            }
        }
        fprintf(stderr, "[analyze] [queue] [len %d]\n", g_queue_get_length(mod_manager->modifications));
    } else {
        // TODO: collect only delta, use feedback
    }
    // Select one modification
    g_array_append_val(mod_manager->done, mod_manager->current);
    mod_manager->current = g_queue_pop_head(mod_manager->modifications);
    // Finished: reset shared_trace_data
    memset(shared_trace_data, 0, sizeof(SharedTraceData));
    // TODO: restore file offset if needed
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
            fprintf(stderr, "[forkserver] [error] parent (fuzzolic) dead?\n");
            exit(2);
        }
    
        /* Establish a channel with child to grab translation commands. We'll
        read from t_fd[0], child will write to TSL_FD. */

        // if (pipe(t_fd) || dup2(t_fd[1], TSL_FD) < 0) exit(3);
        // close(t_fd[1]);

        child_pid = fork();
        if (child_pid < 0) exit(4);

        if (!child_pid) {
#ifdef SNAPSHOT_DEBUG
            snapshot_install_crash_handler();
#endif
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

    
        /* Parent. */
    
        if (write(FORKSRV_FD + 1, &child_pid, 4) != 4) exit(5);
    
        /* Collect translation requests until child dies and closes the pipe. */
    
        // afl_wait_tsl(cpu, t_fd[0]);
    
        /* Get and relay exit status to parent. */
    
        if (waitpid(child_pid, (int *)&status, 0) < 0) exit(6);
        
        // Child process exit
        analyze_collected_data();
    
        // Send exit status
        if (write(FORKSRV_FD + 1, &status, 4) != 4) exit(7);
  
    }

}
