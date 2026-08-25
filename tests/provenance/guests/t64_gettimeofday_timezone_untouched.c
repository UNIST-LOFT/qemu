/* QEMU linux-user gettimeofday writes only the timeval output and ignores the
 * obsolete timezone argument.  A pointer tag stored in that argument must not
 * be invalidated by the post-syscall provenance hook. */
#include <stdint.h>
#include <stdlib.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <unistd.h>

int main(void)
{
    char *p = malloc(16);
    struct timeval tv;
    uint64_t timezone_slot;

    if (!p) {
        return 60;
    }
    free(p);
    timezone_slot = (uint64_t)(uintptr_t)p;
    if (syscall(SYS_gettimeofday, &tv, &timezone_slot) != 0) {
        return 61;
    }

    volatile char value = *(char *)(uintptr_t)timezone_slot;
    (void)value;
    return 0;
}
