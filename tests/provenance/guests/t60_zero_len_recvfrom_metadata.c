/* t60: zero-length socket receive still updates output metadata.  A
 * zero-length datagram writes no payload bytes (the payload tag must
 * survive), but the kernel still writes the in/out addrlen word (the
 * addrlen tag must be invalidated).  Runs with BINRADAR_PROVENANCE_DEBUG=1:
 * the addrlen reload must not produce a consistency-mismatch log, which
 * would mean the invalidation hook was missing and only the value check
 * dropped the tag. */
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
    if (sendto(fds[1], "", 0, 0, NULL, 0) < 0) return 61;
    struct {
        char buf[16];
        uint64_t slot;   /* offset 16: payload-beyond tag */
    } s;
    s.slot = (uint64_t)p;
    union {
        uint64_t tag;
        struct { uint32_t addrlen; uint32_t pad; } w;
    } al;
    al.tag = (uint64_t)p;   /* addrlen word = low 4 bytes of this slot */
    char dummy[16];
    ssize_t r = recvfrom(fds[0], s.buf, 16, 0, (struct sockaddr *)dummy,
                         &al.w.addrlen);
    if (r != 0) return 62;
    /* payload tag must survive (0 bytes written) */
    uint64_t y = s.slot;
    volatile char c = ((char *)y)[0];   /* UAF at p+0 */
    (void)c;
    /* addrlen word must be invalidated (kernel wrote 0) */
    if (al.tag != 0) return 63;
    return 0;
}
