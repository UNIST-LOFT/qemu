/* t57: a failed syscall must leave an existing pointer tag intact.
 * The old code invalidated the stat buffer unconditionally; a failed
 * stat() must not clear the tag stored inside its output buffer, so the
 * later use is UAF. */
#include <stdint.h>
#include <stdlib.h>
#include <sys/stat.h>

int main(void) {
    char *p = malloc(16);
    if (!p) return 60;
    free(p);
    char *buf = malloc(152);
    if (!buf) return 61;
    *(uint64_t *)buf = (uint64_t)p;   /* tag inside the stat output range */
    if (stat("/nonexistent-path-xyz", (struct stat *)buf) == 0) return 62;
    uint64_t y = *(uint64_t *)buf;    /* tag must survive the failure */
    volatile char c = ((char *)y)[0]; /* UAF at p+0 */
    (void)c;
    return 0;
}
