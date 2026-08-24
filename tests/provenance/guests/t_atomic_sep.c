#include <stdint.h>
/* Force a TB boundary between the store and the atomic XORs
 * by using a label/branch. If memcheck_instrument_tb only corrupts
 * atomic ops when they share a TB with instrumented qemu_ld/st,
 * this should exit 0 under memcheck. */
int main(void) {
    uintptr_t slot = UINT64_C(0x123456789abcdef0);
    volatile uintptr_t *p = &slot;
    __asm__ volatile (
        "lock xorq $1, %0\n\t"
        "lock xorq $1, %0"
        : "+m" (*p)
        :
        : "cc", "memory");
    return (int)(*p != UINT64_C(0x123456789abcdef0) ? 21 : 0);
}
