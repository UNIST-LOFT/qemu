/* t48: sticky first-finding policy.  The first crossing store's raw UNKNOWN
 * fallback is promoted by its matching semantic tagged check.  A later
 * unrelated tagged UAF at a different address must not displace that first
 * tagged finding.  The crossing store stays within a readable mapped page,
 * so the guest reaches deferred finalization. */
#include <stdint.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>

int main(void) {
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    char *q = malloc(page * 2);
    if (!q) return 20;

    size_t size = page - ((uintptr_t)q & (page - 1));
    if (size < 32) size += page;
    q = realloc(q, size);
    if (!q || (((uintptr_t)q + size) & (page - 1)) != 0) return 21;
    if (mprotect(q + size, page, PROT_READ | PROT_WRITE) != 0) return 22;

    /* First access: UNKNOWN 8-byte store crossing the object end.  The
     * fallback records the OOB against the tracked q region. */
    __asm__ volatile(
        "movq $0, (%0)" : : "r"(q + size - 4) : "memory");

    /* Second access: tagged UAF at a DIFFERENT address (p freed). */
    char *p = malloc(16);
    if (!p) return 23;
    free(p);
    p[8] = 1; /* tagged UAF store, unrelated address */
    return 0;
}
