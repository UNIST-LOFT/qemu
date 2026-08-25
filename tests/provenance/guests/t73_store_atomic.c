/* t73: a lock-prefixed atomic store of identical pointer bytes must
 * still remove the stale pointer shadow.
 *
 * The atomic xchg writes the full pointer value back unchanged; only the
 * shadow invalidation (not a byte change) can remove the slot's entry.
 * The 8-byte reload re-reads the identical pointer value; a surviving
 * entry would pass value-consistency and restore the tag, making the
 * freed-address access a UAF finding.  The access must not be UAF.
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
    __asm__ volatile("lock xchgq %1, %0"
                     : "+m"(*(uintptr_t *)&slot) : "r"(untagged) : "memory");
    char *q;
    __asm__ volatile("movq %1, %0" : "=r"(q) : "m"(slot) : "memory");
    q[0] = 1; /* must NOT be UAF: the atomic store removed the shadow */
    return 0;
}
