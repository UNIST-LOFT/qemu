/* t09: calloc(SIZE_MAX, 2) overflows: no wrapped-size object may be
 * created; the write must not produce a finding (NULL → UNKNOWN). */
#include <stdint.h>
#include <stdlib.h>

int main(void) {
    void *p = calloc(SIZE_MAX, 2);
    if (p) {
        ((volatile char *)p)[0] = 1;
    }
    return 0;
}
