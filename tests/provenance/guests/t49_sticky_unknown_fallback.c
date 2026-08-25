/* t49: UNKNOWN fallback stickiness.  The first access is an 8-byte
 * crossing store whose address value is UNKNOWN (smashed through int-sized
 * stores so the pointer memory shadow is cleared), producing the
 * exact-bounds fallback.  A later tagged UAF at a different address must
 * NOT displace it.  The next page is mapped read-write so both probes
 * execute without a real signal. */
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
     * pointer value is passed through int-sized stores, which clear the
     * pointer memory shadow (int overwrite clears), so the reloaded
     * register is untagged. */
    uintptr_t target = (uintptr_t)(q + size - 4);
    volatile uintptr_t slot;
    ((volatile uint32_t *)&slot)[0] = (uint32_t)target;
    ((volatile uint32_t *)&slot)[1] = (uint32_t)(target >> 32);
    uintptr_t untagged = slot;
    __asm__ volatile(
        "movq $0, (%0)" : : "r"(untagged) : "memory");

    /* Second access: tagged UAF at a DIFFERENT address (p freed). */
    char *p = malloc(16);
    if (!p) return 23;
    free(p);
    p[8] = 1; /* tagged UAF store, unrelated address */
    return 0;
}
