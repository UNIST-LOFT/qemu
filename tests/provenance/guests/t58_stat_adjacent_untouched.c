/* t58: stat output must invalidate exactly sizeof(struct target_stat)
 * (144 bytes on x86-64), not a conservative 256-byte window.  A tagged
 * pointer placed at buf+144 must survive the successful stat. */
#include <stdint.h>
#include <stdlib.h>
#include <sys/stat.h>

int main(void) {
    char *p = malloc(16);
    if (!p) return 60;
    free(p);
    char *buf = malloc(152);
    if (!buf) return 61;
    *(uint64_t *)(buf + 144) = (uint64_t)p;  /* tag at buf+144, just past stat */
    if (stat("/", buf) != 0) return 62;
    uint64_t y = *(uint64_t *)(buf + 144);   /* must be preserved */
    volatile char c = ((char *)y)[0];         /* UAF at p+0 */
    (void)c;
    return 0;
}
