/* t72: a 16-byte SSE store of identical pointer bytes must still remove
 * the stale pointer shadow.
 *
 * The store covers two aligned pointer slots with the identical pointer
 * value.  Both slots hold tags before the store and both are reloaded
 * afterward.  A surviving shadow entry would pass value-consistency and
 * restore the tag, making its freed-address access a UAF finding.  Both
 * accesses must remain UNKNOWN, proving that the store invalidated every
 * overlapping pointer slot rather than only the first one.
 */
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>

int main(void) {
    int fds[2];
    char *p = malloc(16);
    if (!p || pipe(fds) != 0) return 80;
    void *slots[2] __attribute__((aligned(16))) = {p, p};
    uintptr_t raw = (uintptr_t)p;
    uintptr_t untagged = 0;
    if (write(fds[1], &raw, sizeof(raw)) != (ssize_t)sizeof(raw)) return 81;
    if (read(fds[0], &untagged, sizeof(untagged)) != (ssize_t)sizeof(untagged)) return 82;
    free(p);
    __asm__ volatile(
        "movq %1, %%xmm0\n\t"
        "movq %2, %%xmm1\n\t"
        "punpcklqdq %%xmm1, %%xmm0\n\t"
        "movdqu %%xmm0, %0"
        : "=m"(*(unsigned char (*)[16])slots)
        : "r"(untagged), "r"(untagged)
        : "xmm0", "xmm1", "memory");
    char *q0;
    char *q1;
    __asm__ volatile("movq %1, %0" : "=r"(q0) : "m"(slots[0]) : "memory");
    __asm__ volatile("movq %1, %0" : "=r"(q1) : "m"(slots[1]) : "memory");
    q0[0] = 1;
    q1[0] = 2; /* neither access may retain either slot's stale UAF tag */
    return 0;
}
