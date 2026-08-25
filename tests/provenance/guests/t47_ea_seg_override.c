/* t47b: explicit segment override suppresses semantic EA propagation.
 * `%ds:` is the default segment and emits no prefix, so this test uses
 * `%gs:` — a real override prefix (0x65) that makes the translator record
 * `override >= 0`, excluding the instruction from identity propagation.
 * The guest GS base is 0 in linux-user flat mode, so the effective address
 * equals the register value.  The OOB access starts inside the object
 * (q + 12) and crosses its end.  This guest runs in symbolic mode, where
 * the raw pass is disabled, so obj_id 0 proves the semantic helper still
 * performs UNKNOWN exact-bounds fallback instead of skipping the form.
 */
#include <stdlib.h>

int main(void) {
    char *q = malloc(16);
    if (!q) return 20;

    __asm__ volatile(
        "movq %%gs:12(%0), %%rax"
        : : "r"(q)
        : "rax", "memory");
    return 0;
}
