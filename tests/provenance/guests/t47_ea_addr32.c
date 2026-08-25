/* t47c: address-size override (addr32) truncates the effective address
 * to 32 bits; such truncating modes are excluded from identity
 * propagation.  Guest addresses here are below 4 GiB, so the truncation
 * is value-preserving.  This guest runs in symbolic mode, where obj_id 0
 * proves the semantic helper still performs UNKNOWN exact-bounds fallback
 * for the crossing access instead of skipping the unsupported form.
 */
#include <stdint.h>
#include <stdlib.h>

int main(void) {
    char *q = malloc(16);
    if (!q) return 20;

    __asm__ volatile(
        "addr32 movq 12(%%ebx), %%rax"
        : : "b"((uint32_t)(uintptr_t)q)
        : "rax", "memory");
    return 0;
}
