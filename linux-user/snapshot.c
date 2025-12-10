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
    g_snapshot.cpu_state = malloc(sizeof(CPUArchState));
    memset(g_snapshot.cpu_state, 0, sizeof(CPUArchState));
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

void snapshot_save(CPUArchState *cpu) {
    if (g_snapshot.pages == NULL) snapshot_init();
    if (g_snapshot.is_snapshot_taken) return;
    fprintf(stderr, "[snapshot] [mem] [start]\n");
    // CPU state
    if (g_snapshot.cpu_state) {
        fprintf(stderr, "[snapshot] [cpu] [at %lx] [size %ld]\n", (uintptr_t)cpu, sizeof(CPUArchState));
        memcpy(g_snapshot.cpu_state, cpu, sizeof(CPUArchState));
    }
    // Memory
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

void snapshot_restore(CPUArchState *cpu) {
    // CPU state
    restoring_to_snapshot = true;
    if (g_snapshot.cpu_state) {
        fprintf(stderr, "[snapshot] [restore-cpu]\n");
        memcpy(cpu, g_snapshot.cpu_state, sizeof(CPUArchState));
    }
    
    SnapshotTLS *tls = get_tls();
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

void snapshot_forkserver(CPUState *cpu) {
    fprintf(stderr, "[snapshot] [forkserver] [called %d]\n", forkserver_installed);
    if (forkserver_installed) return;
    forkserver_installed = true;
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
