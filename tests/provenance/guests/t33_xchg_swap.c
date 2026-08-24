/* t33: full-width register xchg must swap the tags with the values.
 * The freed pointer's tag must follow the value into the other register
 * and report UAF on use (§4: xchg → swap the tags). */
#include <stdlib.h>

int main(void) {
    char *p = malloc(16);
    if (!p) return 0;
    free(p);
    char *q = NULL;
    __asm__ volatile("xchg %0, %1" : "+r"(p), "+r"(q) : : "memory");
    q[0] = 1; /* UAF: the tag must follow the value through xchg */
    return 0;
}
