#include "symbolic-transport.h"

#include <sys/ipc.h>
#include <sys/mman.h>
#include <sys/shm.h>
#include <time.h>

static void *symbolic_transport_local_mapping(size_t size)
{
    void *mapping = mmap(NULL, size, PROT_READ | PROT_WRITE,
                         MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    return mapping == MAP_FAILED ? NULL : mapping;
}

static int symbolic_transport_wait_shm(key_t key, size_t size)
{
    const struct timespec pause = {.tv_nsec = 50};
    int id;
    do {
        id = shmget(key, size, 0666 | IPC_CREAT);
        if (id >= 0) return id;
        nanosleep(&pause, NULL);
    } while (true);
}

bool symbolic_transport_open(SymbolicTransport *transport,
                             const SymbolicConfig *config)
{
    if (transport == NULL || config == NULL) return false;
    memset(transport, 0, sizeof(*transport));
    transport->external_solver = !config->no_external_solver;
    if (!transport->external_solver) {
        transport->expression_pool = symbolic_transport_local_mapping(
            sizeof(Expr) * EXPR_POOL_CAPACITY);
        transport->query_queue = symbolic_transport_local_mapping(
            sizeof(Query) * EXPR_QUERY_CAPACITY);
#if BRANCH_COVERAGE == FUZZOLIC
        transport->branch_bitmap = symbolic_transport_local_mapping(
            sizeof(uint8_t) * BRANCH_BITMAP_SIZE);
#endif
    } else {
        int expression_id = symbolic_transport_wait_shm(
            (key_t)config->expr_pool_shm_key,
            sizeof(Expr) * EXPR_POOL_CAPACITY);
        int query_id = symbolic_transport_wait_shm(
            (key_t)config->query_shm_key,
            sizeof(Query) * EXPR_QUERY_CAPACITY);
        transport->expression_pool = shmat(
            expression_id, EXPR_POOL_ADDR, 0);
        transport->query_queue = shmat(query_id, NULL, 0);
#if BRANCH_COVERAGE == FUZZOLIC
        int bitmap_id = symbolic_transport_wait_shm(
            (key_t)config->bitmap_shm_key,
            sizeof(uint8_t) * BRANCH_BITMAP_SIZE);
        transport->branch_bitmap = shmat(bitmap_id, NULL, 0);
#endif
        if (transport->expression_pool == (void *)-1 ||
            transport->query_queue == (void *)-1 ||
            transport->branch_bitmap == (void *)-1) {
            return false;
        }
    }
    return transport->expression_pool != NULL &&
           transport->query_queue != NULL
#if BRANCH_COVERAGE == FUZZOLIC
           && transport->branch_bitmap != NULL
#endif
           ;
}

bool symbolic_transport_wait_ready(const SymbolicTransport *transport)
{
    if (transport == NULL || transport->query_queue == NULL) return false;
    if (!transport->external_solver) return true;
    const struct timespec pause = {.tv_nsec = 50};
    while (transport->query_queue[0].query != (void *)SHM_READY) {
        nanosleep(&pause, NULL);
    }
    return true;
}
