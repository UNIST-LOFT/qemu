/* t11: realloc shrink keeps the new object valid; access within the new
 * size must not be a finding. */
#include <stdlib.h>

int main(void) {
    char *p = malloc(128);
    if (!p) return 0;
    char *q = realloc(p, 16);
    if (!q) return 0;
    q[0] = 1;
    free(q);
    return 0;
}
