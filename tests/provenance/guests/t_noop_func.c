#include <stdint.h>
static volatile uintptr_t slot;
__attribute__((noinline))
static void do_noop(void) {
    /* No atomic — just read and write the global */
    slot ^= 1;
    slot ^= 1;
}
int main(void) {
    slot = UINT64_C(0x123456789abcdef0);
    do_noop();
    return (int)(slot != UINT64_C(0x123456789abcdef0) ? 21 : 0);
}
