/* A modeled strcpy whose destination crosses into PROT_NONE must leave the
 * real target fault in charge and must not publish a pre-access OOB finding. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

int main(void)
{
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    char *p = malloc(page * 2);
    if (!p) {
        return 102;
    }

    size_t size = page - ((uintptr_t)p & (page - 1));
    if (size < 32) {
        size += page;
    }
    char *q = realloc(p, size);
    if (!q || (((uintptr_t)q + size) & (page - 1)) != 0) {
        return 103;
    }
    if (mprotect(q + size, page, PROT_NONE) != 0) {
        return 104;
    }

    strcpy(q + size - 4, "ABCDEFGH");
    return 105;
}
