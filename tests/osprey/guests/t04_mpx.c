/* t04_mpx: successful MPX semantic-event regression fixture.
 *
 * The selected user-mode CPU advertises MPX, but the guest state is initially
 * disabled for the bounds directory.  XRSTOR loads both MPX state components
 * from a crafted standard-format image, enabling the directory.  BNDMOV,
 * BNDSTX, and BNDLDX then exercise the translator and helper-backed F01 paths
 * against main-image writable storage.
 */
#include <stdint.h>
#include <string.h>

static volatile uint64_t g_sink;

static uint8_t xsave_image[0x440] __attribute__((aligned(64)));
static uint8_t bounds_directory[4096] __attribute__((aligned(1 << 20)));
static uint8_t bounds_table[4096] __attribute__((aligned(4096)));
static uint8_t target_page[4096] __attribute__((aligned(4096)));
static uint64_t bound_pair[2] __attribute__((aligned(16)));
static uint64_t loaded_pair[2] __attribute__((aligned(16)));

static int enable_mpx(void)
{
    uint64_t *const header_xstate_bv =
        (uint64_t *)(xsave_image + 0x200);
    uint64_t *const bndcfg = (uint64_t *)(xsave_image + 0x400);
    uint64_t mask = (1ULL << 3) | (1ULL << 4);

    memset(xsave_image, 0, sizeof(xsave_image));
    *header_xstate_bv = mask;
    /* lookup_bte64() reconstructs the directory base from the encoded
     * BNDCFGS field (bits 63:20), so encode the 4-KiB base accordingly. */
    *bndcfg = ((uintptr_t)bounds_directory << 8) | 3ULL;
    __asm__ volatile(
        ".globl t04_mpx_enable\n"
        "t04_mpx_enable:\n"
        "xrstor %0\n"
        :
        : "m"(*(const uint8_t (*)[0x440])xsave_image),
          "a"((uint32_t)mask), "d"((uint32_t)(mask >> 32))
        : "memory");

    /* The directory index is zero because the MIB base is zero below. */
    *(uint64_t *)bounds_directory = (uintptr_t)bounds_table | 1ULL;
    *(uint64_t *)(bounds_table + 0) = (uintptr_t)target_page;
    *(uint64_t *)(bounds_table + 8) = (uintptr_t)target_page + 0x100;
    *(uint64_t *)(bounds_table + 16) = (uintptr_t)target_page;
    bound_pair[0] = (uintptr_t)target_page;
    bound_pair[1] = (uintptr_t)target_page + 0x100;
    return 0;
}

static void bndmov_roundtrip(void)
{
    __asm__ volatile(
        ".globl t04_bndmov_load\n"
        "t04_bndmov_load:\n"
        "bndmov %0, %%bnd0\n"
        :
        : "m"(*(const uint64_t (*)[2])bound_pair)
        : "memory");
    __asm__ volatile(
        ".globl t04_bndmov_store\n"
        "t04_bndmov_store:\n"
        "bndmov %%bnd0, %0\n"
        : "=m"(*(uint64_t (*)[2])loaded_pair)
        :
        : "memory");
}

static void bnd_table_roundtrip(void)
{
    register uintptr_t mib_base __asm__("rax") = 0;
    register uintptr_t pointer __asm__("rcx") = (uintptr_t)target_page;

    __asm__ volatile(
        ".globl t04_bndstx\n"
        "t04_bndstx:\n"
        "bndstx %%bnd0, (%%rax,%%rcx)\n"
        :
        : "a"(mib_base), "c"(pointer)
        : "memory");
    __asm__ volatile(
        ".globl t04_bndldx\n"
        "t04_bndldx:\n"
        "bndldx (%%rax,%%rcx), %%bnd0\n"
        :
        : "a"(mib_base), "c"(pointer)
        : "memory");
    __asm__ volatile(
        ".globl t04_bndmov_after_load\n"
        "t04_bndmov_after_load:\n"
        "bndmov %%bnd0, %0\n"
        : "=m"(*(uint64_t (*)[2])loaded_pair)
        :
        : "memory");
    g_sink ^= loaded_pair[0] ^ loaded_pair[1];
}

int main(void)
{
    if (enable_mpx() != 0) {
        return 10;
    }
    bndmov_roundtrip();
    bnd_table_roundtrip();
    return (int)(g_sink & 1);
}
