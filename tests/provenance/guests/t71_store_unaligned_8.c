/* t71: an unaligned 8-byte store must still remove the stale pointer
 * shadow.
 *
 * The store writes P>>8 at slot+1 (8 bytes, unaligned).  That leaves
 * slot's 8 bytes bit-identical to the original pointer P: byte 0 of
 * slot is untouched and bytes 1..7 receive P's bytes 0..6.  The shadow
 * only tracks aligned slots, so the entry at slot can only be removed
 * by the store's overlap invalidation — never by a byte change.  The
 * 8-byte reload re-reads P; a surviving entry would pass value-
 * consistency and restore the tag, making the freed-address access a
 * UAF finding.  The access must not be UAF.
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
    uintptr_t shifted = untagged >> 8;
    __asm__ volatile("movq %1, 1(%0)"
                     : : "r"(&slot), "r"(shifted) : "memory");
    char *q;
    __asm__ volatile("movq %1, %0" : "=r"(q) : "m"(slot) : "memory");
    q[0] = 1; /* must NOT be UAF: the unaligned store removed the shadow */
    return 0;
}
