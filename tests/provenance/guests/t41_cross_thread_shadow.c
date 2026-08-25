/* A pointer spilled by one guest thread must reload with identity in another. */
#include <pthread.h>
#include <stdatomic.h>
#include <stdlib.h>

static void *shared_slot;
static atomic_int go;

static void *worker(void *unused) {
    (void)unused;
    while (!atomic_load_explicit(&go, memory_order_acquire)) { }
    char *p = shared_slot;
    p[0] = 1;
    return NULL;
}

int main(void) {
    pthread_t thread;
    char *p = malloc(24);
    if (!p) return 50;
    shared_slot = p;
    if (pthread_create(&thread, NULL, worker, NULL) != 0) return 51;
    free(p);
    atomic_store_explicit(&go, 1, memory_order_release);
    if (pthread_join(thread, NULL) != 0) return 52;
    return 0;
}
