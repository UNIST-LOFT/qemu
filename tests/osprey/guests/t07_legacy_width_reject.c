/* t07_legacy_width_reject: x86-64 target gate for legacy x87 widths.
 *
 * The 0x66-prefixed environment/save forms are only accepted as positive
 * F01 coverage in an i386 user target.  This x86-64-only harness executes
 * both forms and requires the translator to reject the OSPREY sample without
 * publishing a 14- or 94-byte access row.
 */
#include <stdint.h>

static uint8_t env_image[108] __attribute__((aligned(16)));

static void legacy_widths(void)
{
    __asm__ volatile(
        ".globl t07_fnstenvw\n"
        "t07_fnstenvw:\n"
        ".byte 0x66\n"
        "fnstenv %0"
        : "=m"(*(uint8_t (*)[14])env_image));
    __asm__ volatile(
        ".globl t07_fnsavew\n"
        "t07_fnsavew:\n"
        ".byte 0x66\n"
        "fnsave %0"
        : "=m"(*(uint8_t (*)[94])(env_image + 16)));
}

int main(void)
{
    legacy_widths();
    return env_image[0] == 0xff;
}
