/* t47a: tagged base + untagged runtime index (scale 8) exercises the
 * retained compatibility fold.  The helper first reconstructs the exact
 * target-width EA from base, index, scale, and displacement; only a match
 * permits the runtime delta to update the checked tag offset.  The access
 * at q + 4 + 8*1 starts inside the object and crosses its end, so the
 * resulting finding must retain obj_id 1 at offset 12.
 */
#include <stdint.h>
#include <stdlib.h>

int main(void) {
    char *q = malloc(16);
    if (!q) return 20;

    __asm__ volatile(
        "movq 4(%0,%1,8), %%rax"
        : : "r"(q), "r"((uintptr_t)1)
        : "rax", "memory");
    return 0;
}
