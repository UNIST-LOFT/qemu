/* t70: a 4-byte store of identical pointer bytes must still remove the
 * stale pointer shadow.
 *
 * Proof of removal (not byte change): the store writes the low 32 bits
 * of the freed pointer back unchanged, then an 8-byte reload of the slot
 * re-reads the identical pointer value.  A surviving shadow entry would
 * pass the value-consistency check and restore the tag, making the
 * freed-address access a UAF finding.  Only the store's overlap
 * invalidation can make the reload UNKNOWN, so the access must not be
 * UAF.
 */
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>

int main(void) {
    int fds[2];
    char *p = malloc(16);
    if (!p || pipe(fds) != 0) return 80;
    void *slot __attribute__((aligned(16))) = p;
    uintptr_t raw = (uintptr_t)p;
    uintptr_t untagged = 0;
    if (write(fds[1], &raw, sizeof(raw)) != (ssize_t)sizeof(raw)) return 81;
    if (read(fds[0], &untagged, sizeof(untagged)) != (ssize_t)sizeof(untagged)) return 82;
    free(p);
    __asm__ volatile("movl %k1, %0"
                     : "=m"(*(unsigned int *)&slot)
                     : "r"((unsigned int)untagged)
                     : "memory");
    char *q;
    __asm__ volatile("movq %1, %0" : "=r"(q) : "m"(slot) : "memory");
    q[0] = 1; /* must NOT be UAF: the 4-byte store removed the shadow */
    return 0;
}
