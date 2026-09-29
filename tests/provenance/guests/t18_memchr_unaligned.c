/* t18: memchr on an unaligned heap buffer, fully inside the object and
 * crossing the symbolic shadow's internal 64-KiB page boundary: must not
 * read past one metadata page or report a finding. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

int main(void) {
    const size_t page = 64 * 1024;
    const size_t length = 4096;
    char *p = malloc(2 * page + length);
    if (!p) return 0;
    uintptr_t boundary = ((uintptr_t)p + length / 2 + page - 1) &
                         ~(page - 1);
    char *start = (char *)(boundary - length / 2);
    memset(start, 1, length);
    /* Unaligned to the allocation and split equally across shadow pages. */
    if (memchr(start, 0, length) == NULL) {
        /* still exercised the model */
    }
    free(p);
    return 0;
}
