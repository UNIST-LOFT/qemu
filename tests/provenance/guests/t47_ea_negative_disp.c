/* t47d: a negative constant displacement is x86 target-width wrapping
 * address arithmetic, not an unsigned-overflow failure.  The access at q-1
 * starts outside the live object, so UNKNOWN fallback cannot find it; the
 * tagged [base + disp] rule must report obj_id 1, offset -1, width 1.
 */
#include <stdlib.h>

int main(void) {
    char *q = malloc(16);
    if (!q) return 20;

    __asm__ volatile(
        "movb -1(%0), %%al"
        : : "r"(q)
        : "rax", "memory");
    return 0;
}
