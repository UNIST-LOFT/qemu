/* t63: recvmsg header outputs.  The kernel writes the returned
 * msg_namelen and msg_flags fields (0 for a plain datagram on an
 * unconnected socketpair).  Tags pre-stored in those fields must be
 * invalidated; the payload tag beyond the returned bytes must survive.
 * Runs with BINRADAR_PROVENANCE_DEBUG=1: the header-field reloads must
 * not produce consistency-mismatch logs, which would mean the
 * invalidation hook was missing and only the value check dropped the
 * tags. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>

int main(void) {
    int fds[2];
    char *p = malloc(16);
    if (!p || socketpair(AF_UNIX, SOCK_DGRAM, 0, fds) != 0) return 60;
    free(p);
    unsigned long payload = (unsigned long)p;
    if (sendto(fds[1], &payload, 8, 0, NULL, 0) != 8) return 61;
    struct {
        char iov0[16];
        uint64_t slot;   /* offset 16: payload-beyond tag */
    } r;
    r.slot = (uint64_t)p;
    struct iovec riov[1] = {{r.iov0, 16}};
    struct msghdr msg;
    memset(&msg, 0, sizeof(msg));
    msg.msg_iov = riov; msg.msg_iovlen = 1;
    /* corrupt the in/out header fields with the pointer tag */
    *(uint64_t *)((char *)&msg + 8) = (uint64_t)p;   /* msg_namelen */
    *(uint64_t *)((char *)&msg + 48) = (uint64_t)p;  /* msg_flags */
    ssize_t rv = recvmsg(fds[0], &msg, 0);
    if (rv != 8) return 62;
    /* header fields must be invalidated (kernel wrote 0) */
    if (*(uint64_t *)((char *)&msg + 8) != 0) return 63;
    if (*(uint64_t *)((char *)&msg + 48) != 0) return 64;
    /* payload-beyond tag must survive (only 8 bytes written) */
    uint64_t y = r.slot;
    volatile char c = ((char *)y)[0];   /* UAF at p+0 */
    (void)c;
    return 0;
}
