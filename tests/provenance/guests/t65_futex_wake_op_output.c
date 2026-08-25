/* FUTEX_WAKE_OP is the only futex operation implemented by this QEMU version
 * that writes guest memory.  Its encoded operation updates the low 32 bits at
 * uaddr2, which must invalidate an overlapping pointer-shadow slot. */
#include <linux/futex.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/syscall.h>
#include <unistd.h>

int main(void)
{
    char *p = malloc(16);
    uint32_t wake_word = 0;
    union {
        uint64_t tag;
        struct {
            uint32_t word;
            uint32_t padding;
        } parts;
    } output;
    long ret;

    if (!p) {
        return 60;
    }
    free(p);
    output.tag = (uint64_t)(uintptr_t)p;

    ret = syscall(SYS_futex, &wake_word,
                  FUTEX_WAKE_OP | FUTEX_PRIVATE_FLAG, 0, 0,
                  &output.parts.word,
                  FUTEX_OP(FUTEX_OP_SET, 1, FUTEX_OP_CMP_EQ, 0));
    if (ret < 0 || output.parts.word != 1) {
        return 61;
    }

    /* Force a provenance reload.  Without the syscall hook this produces a
     * consistency-mismatch repair because the concrete low word changed. */
    volatile uint64_t observed = output.tag;
    if ((uint32_t)observed != 1) {
        return 62;
    }
    return 0;
}
