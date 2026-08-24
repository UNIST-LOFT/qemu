/* t35: a successful realloc retires the old identity and creates a new
 * one, even when the numeric address is unchanged.  The old pointer must
 * report UAF against the old identity (§3: same-address realloc → old
 * identity FREED, returned pointer has a new LIVE identity). */
#include <stdlib.h>

int main(void) {
    char *p = malloc(64);
    if (!p) return 0;
    char *q = realloc(p, 32);
    if (!q) return 0;
    /* Old pointer: UAF whether realloc moved (old object freed) or kept
     * the address (old identity retired, new identity created). */
    p[0] = 1;
    free(q);
    return 0;
}
