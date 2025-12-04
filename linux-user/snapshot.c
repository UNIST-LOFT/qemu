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

    GList *l;
    for (l = g_snapshot.new_mappings; l != NULL; l = l->next) {
        // pair: {addr, len} 구조체가 필요함 (간략화)
        // target_munmap(item->addr, item->len); 
        // 실제 구현 시 struct로 관리 필요
    }
    g_list_free(g_snapshot.new_mappings);
    g_snapshot.new_mappings = NULL;

    // 2. BRK 복구
    if (target_brk != g_snapshot.start_brk) {
        target_brk = g_snapshot.start_brk;
        // 실제 brk syscall 로직 호출하여 힙 줄이기 필요
    }

    // 3. Dirty Page 복구 (핵심)
    GHashTableIter iter;
    gpointer key, value;
    g_hash_table_iter_init(&iter, tls->dirty_pages);

    while (g_hash_table_iter_next(&iter, &key, &value)) {
        target_ulong addr = *(target_ulong*)key;
        
        // 스냅샷 데이터 조회
        SnapshotPageInfo *info = g_hash_table_lookup(g_snapshot.pages, &addr);
        if (info) {
            // 원본 데이터로 덮어쓰기
            void *host_addr = g2h(addr);
            
            // 페이지 권한이 Read-Only로 바뀌었을 수도 있으므로 강제 Write 권한 부여 필요할 수 있음
            // mprotect(host_addr, SNAPSHOT_PAGE_SIZE, PROT_READ | PROT_WRITE); 
            
            memcpy(host_addr, info->data, SNAPSHOT_PAGE_SIZE);
        } else {
            // 스냅샷에 없는데 Dirty? -> 스냅샷 이후 새로 할당된 페이지이거나 스킵된 페이지
            // Rust 코드에서는 zero-fill 하거나 무시함.
            // 여기서는 memset 0 처리
            void *host_addr = g2h(addr);
            memset(host_addr, 0, SNAPSHOT_PAGE_SIZE);
        }
    }

    // Dirty Set 초기화
    g_hash_table_remove_all(tls->dirty_pages);
    // Cache 초기화
    for(int i=0; i<4; i++) tls->access_cache[i] = -1;
}

// Syscall Hook: mmap
void snapshot_syscall_mmap(target_ulong addr, target_ulong len, int prot) {
    // 새로 할당된 영역 추적
    // Rust의 add_mapped 대응
    // g_list_append(g_snapshot.new_mappings, create_mapping_info(addr, len));
    // 그리고 해당 영역을 Dirty로 표시하여 나중에 접근 추적
}

// Syscall Hook: munmap
// Rust의 is_unmap_allowed 대응
int snapshot_is_unmap_allowed(target_ulong addr, target_ulong len) {
    // 스냅샷에 존재하는 페이지를 munmap 하려고 하면 차단 (퍼징 안정성)
    target_ulong end = addr + len;
    for (target_ulong p = addr; p < end; p += SNAPSHOT_PAGE_SIZE) {
        if (g_hash_table_contains(g_snapshot.pages, &p)) {
            return 0; // False
        }
    }
    return 1; // True
}
