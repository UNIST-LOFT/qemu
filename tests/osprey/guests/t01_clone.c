/* Stage-1 unsupported-execution fixture: a successful pthread clone must
 * reject OSPREY analysis rather than install a model from racy facts. */
#include <pthread.h>
#include <stdint.h>

static volatile uint64_t shared_value;

static void *worker(void *arg)
{
    shared_value = (uintptr_t)arg;
    return NULL;
}

int main(void)
{
    pthread_t thread;
    if (pthread_create(&thread, NULL, worker, (void *)(uintptr_t)0x1234) != 0) {
        return 1;
    }
    if (pthread_join(thread, NULL) != 0) {
        return 1;
    }
    return shared_value == 0x1234 ? 0 : 1;
}
