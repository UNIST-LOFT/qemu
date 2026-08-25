/* readv must invalidate from the vector captured before the syscall.  The
 * first output below overwrites the second guest iovec descriptor; rebuilding
 * destinations from that descriptor after the syscall misses the second
 * output and leaves its identical-byte pointer tag stale. */
#include <stdint.h>
#include <stdlib.h>
#include <sys/uio.h>
#include <unistd.h>

int main(void)
{
    int fds[2];
    char *p = malloc(16);
    uint64_t slot;
    uint64_t input[2];
    struct iovec iov[2];

    if (!p || pipe(fds) != 0) {
        return 60;
    }
    free(p);
    slot = (uint64_t)(uintptr_t)p;
    input[0] = UINT64_C(0x4141414141414141);
    input[1] = slot;

    iov[0].iov_base = &iov[1].iov_base;
    iov[0].iov_len = sizeof(input[0]);
    iov[1].iov_base = &slot;
    iov[1].iov_len = sizeof(slot);

    if (write(fds[1], input, sizeof(input)) != sizeof(input)) {
        return 61;
    }
    if (readv(fds[0], iov, 2) != sizeof(input)) {
        return 62;
    }
    if (slot != (uint64_t)(uintptr_t)p) {
        return 63;
    }

    /* The raw bytes still equal p, but the readv output must have removed the
     * tag.  A stale tag would turn this mapped freed-address read into UAF. */
    volatile char value = *(char *)(uintptr_t)slot;
    (void)value;
    return 0;
}
