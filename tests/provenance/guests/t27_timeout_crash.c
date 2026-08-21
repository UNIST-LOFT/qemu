/* t27: timeout transport: UAF detected in the guest, then an infinite
 * loop. The forkserver parent's child-timeout path must surface the
 * deferred finding from shared memory as a synthetic crash (139 =
 * 128+SIGSEGV) instead of a bare SIGKILL (137). */
#include <stdlib.h>

int main(void) {
    char *p = malloc(8);
    if (!p) return 0;
    free(p);
    for (;;) {
        p[0] = 1; /* UAF on every iteration; never returns */
    }
    return 0;
}
