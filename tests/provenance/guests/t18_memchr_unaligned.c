/* t18: memchr on an unaligned heap buffer, fully inside the object:
 * must not be a finding. */
#include <stdlib.h>
#include <string.h>

int main(void) {
    char *p = malloc(64);
    if (!p) return 0;
    /* unaligned start, in-bounds; search may miss, result unused */
    if (memchr(p + 1, 0, 32) == NULL) {
        /* still exercised the model */
    }
    free(p);
    return 0;
}
