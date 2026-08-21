/* t12: memcpy model: copying more than the destination object holds must
 * be reported as OOB (dst tagged, interval check by the model). */
#include <stdlib.h>
#include <string.h>

int main(void) {
    char *src = malloc(32);
    char *dst = malloc(8);
    if (!src || !dst) return 0;
    memcpy(dst, src, 16); /* 16 > 8 → dst OOB */
    free(src);
    free(dst);
    return 0;
}
