#include <stdint.h>

int main(void) {
    uintptr_t slot = UINT64_C(0x123456789abcdef0);
    __asm__ volatile (
        "lock xorq $1, %0\n\t"
        "lock xorq $1, %0"
        : "+m" (slot)
        :
        : "cc", "memory");
    return slot == UINT64_C(0x123456789abcdef0) ? 0 : 21;
}
