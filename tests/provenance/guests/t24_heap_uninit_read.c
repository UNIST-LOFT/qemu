/* t24: heap uninitialized read: reading uninitialized heap bytes is not
 * a provenance finding (memcheck tracks address, not value).  The read
 * must not influence control flow (deterministic rc). */
#include <stdlib.h>

int main(void) {
    char *p = malloc(8);
    if (!p) return 0;
    volatile char c = p[0]; /* uninitialized read: value-based, not address-based */
    (void)c;
    free(p);
    return 0;
}
