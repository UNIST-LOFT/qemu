/* t59: partial readv invalidates only the returned bytes.  A tagged
 * pointer in the second iovec (beyond the 4 returned bytes) must survive
 * the readv, so the later use is UAF. */
#include <stdint.h>
#include <stdlib.h>
#include <sys/uio.h>
#include <unistd.h>

int main(void) {
    int fds[2];
    char *p = malloc(16);
    if (!p || pipe(fds) != 0) return 60;
    free(p);
    if (write(fds[1], "AAAA", 4) != 4) return 61;
    char buf0[8], buf1[8];
    *(uint64_t *)buf1 = (uint64_t)p;   /* tag in the second iovec */
    struct iovec iov[2] = {{buf0, 8}, {buf1, 8}};
    ssize_t r = readv(fds[0], iov, 2);
    if (r != 4) return 62;
    uint64_t y = *(uint64_t *)buf1;    /* must be preserved */
    volatile char c = ((char *)y)[0];  /* UAF at p+0 */
    (void)c;
    return 0;
}
