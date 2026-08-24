/* t30: popping an untagged stack slot must yield UNKNOWN, not a stale
 * tag.  The slot is overwritten with a non-pointer before the pop; the
 * register must become 0/UNKNOWN (§5: no tag for the slot → UNKNOWN). */
#include <stdint.h>
#include <stdlib.h>

int main(void) {
    char *p = malloc(16);
    if (!p) return 0;
    free(p);
    uintptr_t a = (uintptr_t)p;
    /* Push the freed pointer (tagged slot), overwrite the slot with a
     * non-pointer, pop: the register must become UNKNOWN (0), not keep
     * the freed tag. */
    __asm__ volatile(
        "push %0\n\t"
        "movq $0, (%%rsp)\n\t"
        "pop %0\n\t"
        : "+r"(a) : : "memory");
    if (a != 0) return 0; /* sanity: value must be 0 */
    return 0;
}
