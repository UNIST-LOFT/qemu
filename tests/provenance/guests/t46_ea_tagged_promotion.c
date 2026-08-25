/* t46: tagged-identity promotion through the supported EA form
 * [tagged_base + constant displacement].
 *
 * malloc(24) then an eight-byte load at constant displacement 24:
 * `movq 24(%0), %%rax` with %0 holding q directly — one register, no
 * index, translation-time displacement.  The raw post-op fallback must
 * be promoted by the matching semantic check to the tagged identity
 * (obj_id=1, generation 1, offset 24, width 8), proving the
 * constant-displacement rule retains provenance end to end.
 */
#include <stdlib.h>

int main(void) {
    char *q = malloc(24);
    if (!q) return 20;

    __asm__ volatile("movq 24(%0), %%rax" : : "r"(q) : "rax", "memory");
    return 0;
}
