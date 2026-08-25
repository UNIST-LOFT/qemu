/* x87 helper-backed stores must preserve architectural pop/reset semantics.
 * An identical-byte fstpt store must also clear stale pointer shadow. */
#include <stdint.h>
#include <stdlib.h>

struct env_image { unsigned char bytes[32]; } __attribute__((aligned(16)));
struct save_image { unsigned char bytes[128]; } __attribute__((aligned(16)));

union x87_slot {
    long double value;
    void *pointer;
    unsigned char bytes[16];
} __attribute__((aligned(16)));

static int any_nonzero(const unsigned char *p, unsigned long n) {
    for (unsigned long i = 0; i < n; i++) {
        if (p[i] != 0) return 1;
    }
    return 0;
}

int main(void) {
    struct env_image env = {{0}};
    struct save_image save = {{0}};
    unsigned char ext[16] __attribute__((aligned(16))) = {0};
    unsigned char bcd[10] = {0};
    double value = 12345.0;

    __asm__ volatile("fld1; fnstenv %0" : "=m"(env) : : "memory");
    if (!any_nonzero(env.bytes, 28)) return 31;

    __asm__ volatile("fld1; fstpt %0" : "=m"(*(long double *)ext) : : "memory");
    if (!any_nonzero(ext, 10)) return 32;

    __asm__ volatile("fld1; fnsave %0" : "=m"(save) : : "memory");
    if (!any_nonzero(save.bytes, 108)) return 33;
    __asm__ volatile("fninit" : : : "memory");

    __asm__ volatile("fldl %1; fbstp %0" : "=m"(bcd) : "m"(value) : "memory");
    if (bcd[0] != 0x45 || bcd[1] != 0x23 || bcd[2] != 0x01) return 34;

    char *p = malloc(16);
    if (!p) return 35;
    union x87_slot input = {.pointer = p};
    union x87_slot output = {.pointer = p};
    uintptr_t expected = (uintptr_t)p;
    /* Exponent/sign bytes stay zero: this is an extended-precision denormal,
     * so fldt/fstpt preserve the low pointer bytes exactly. */
    input.bytes[8] = 0;
    input.bytes[9] = 0;
    free(p);
    __asm__ volatile("fldt %1; fstpt %0"
                     : "=m"(output.value) : "m"(input.value) : "memory");
    if ((uintptr_t)output.pointer != expected) return 36;
    volatile char probe = ((char *)output.pointer)[0];
    (void)probe;
    return 0;
}
