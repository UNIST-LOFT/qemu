/* A successful host recvmsg writes payload before QEMU converts ancillary
 * data.  If the later target control copyout fails, the syscall returns
 * EFAULT but the payload output still needs provenance invalidation. */
#include <errno.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/socket.h>
#include <sys/uio.h>
#include <unistd.h>

int main(void)
{
    int fds[2];
    char *p = malloc(16);
    uint64_t payload;
    struct iovec iov;
    struct msghdr msg;

    if (!p || socketpair(AF_UNIX, SOCK_DGRAM, 0, fds) != 0) {
        return 60;
    }
    free(p);
    payload = (uint64_t)(uintptr_t)p;
    if (send(fds[1], &payload, sizeof(payload), 0) != sizeof(payload)) {
        return 61;
    }

    iov.iov_base = &payload;
    iov.iov_len = sizeof(payload);
    msg.msg_name = NULL;
    msg.msg_namelen = 0;
    msg.msg_iov = &iov;
    msg.msg_iovlen = 1;
    msg.msg_control = (void *)1;
    msg.msg_controllen = 32;
    msg.msg_flags = 0;

    errno = 0;
    if (recvmsg(fds[0], &msg, 0) != -1 || errno != EFAULT) {
        return 62;
    }
    if (payload != (uint64_t)(uintptr_t)p) {
        return 63;
    }

    /* Identical payload bytes cannot trigger value-consistency repair.  The
     * syscall copyout hook itself must have removed the stale tag. */
    volatile char value = *(char *)(uintptr_t)payload;
    (void)value;
    return 0;
}
