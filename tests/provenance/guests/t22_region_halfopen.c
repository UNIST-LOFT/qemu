/* t22: region half-open: free() keeps a half-open region that the
 * tracer must NOT treat as a live object.  A write to the freed region
 * is UAF, not OOB: check the finding type stays "use-after-free". */
#include <stdlib.h>

int main(void) {
    char *p = malloc(8);
    if (!p) return 0;
    free(p);
    p[0] = 1; /* freed → region half-open → UAF, not OOB */
    return 0;
}
