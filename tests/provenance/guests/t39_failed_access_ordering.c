/* A raw UNKNOWN candidate staged for a faulting access must never commit. */
#include <stdint.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>

int main(void) {
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    char *p = malloc(page * 2);
    if (!p) return 20;

    size_t size = page - ((uintptr_t)p & (page - 1));
    if (size < 32) size += page;
    char *q = realloc(p, size);
    if (!q || (((uintptr_t)q + size) & (page - 1)) != 0) return 21;
    if (mprotect(q + size, page, PROT_NONE) != 0) return 22;

    __asm__ volatile("movq (%0), %%rax" : : "r"(q + size - 4) : "rax", "memory");
    return 23;
}
