/* t11_modeled_copies: Stage-2.4 modeled byte-copy fixture.
 *
 * Exercises the PLT-model copy paths (memcpy/memmove/strcpy/strncpy/
 * memset) under three distinct PIE load biases:
 *  - memcpy(dst,src,13): one exact 13-byte F03;
 *  - overlapping memmove(buf+8,buf,16): one exact F03; pointer tags
 *    snapshot before destination invalidation;
 *  - strcpy(dst,"abc"): one 4-byte F03 including NUL;
 *  - strncpy(dst,"abc",8): one 4-byte F03; full 8-byte destination
 *    invalidation; no copy row for the four padding bytes;
 *  - strncpy(dst,eight_nonzero,8): one 8-byte F03;
 *  - zero-length memcpy/strncpy: no F03 and no shadow mutation;
 *  - memset over a tagged pointer slot: no F03; overlapping tag
 *    removed;
 *  - preflight-rejected copy into a protected page: no F03/F04;
 *  - memcpy of one aligned tagged pointer slot: F03, destination F04,
 *    relocated ADDRESS slot, and later reload F02.
 *
 * All libc calls are plain -fno-builtin direct calls so they resolve
 * through the PLT stubs the model dispatcher intercepts; the intended
 * model path cannot be folded into inline compiler stores.  String
 * literals live in writable global arrays so their chunks canonicalize
 * in region G.  Registers are fixed with complete clobber lists;
 * _exit(0) avoids shutdown noise.
 */
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

static uint64_t g_src[8] __attribute__((aligned(8)));
static uint64_t g_dst[8] __attribute__((aligned(8)));
static uint64_t g_buf[8] __attribute__((aligned(8)));
static void *g_pointer_slot __attribute__((aligned(8)));
static void *g_pointer_slot2 __attribute__((aligned(8)));
static void *g_heap_ptr;                              /* .bss */
static __attribute__((aligned(4096))) uint8_t g_fault_page[4096];
static char g_str_dst[64] __attribute__((aligned(8)));
static char g_lit_abc[4] = "abc";                     /* .data, modeled */
static char g_lit_eight[9] = "12345678";              /* .data, modeled */

static volatile uint64_t g_sink;
static sigjmp_buf fault_jmp;
static volatile sig_atomic_t fault_seen;

static void fault_handler(int sig)
{
    (void)sig;
    fault_seen = 1;
    siglongjmp(fault_jmp, 1);
}

int main(void)
{
    for (int i = 0; i < 8; i++) {
        g_src[i] = 0x0102030405060708ULL * (uint64_t)(i + 1);
        g_dst[i] = 0;
        g_buf[i] = 0;
    }
    void *p = malloc(64);
    if (!p) {
        _exit(1);
    }
    __asm__ volatile("movq %%rax, g_heap_ptr(%%rip)\n"
                     :: "a"(p) : "memory");

    /* Tagged pointer slot publication (source for the pointer memcpy). */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        ".globl t11_prod_slot_store\n"
        "t11_prod_slot_store:\n\t"
        "movq %%r12, g_pointer_slot(%%rip)\n"
        : : : "r12", "memory");

    /* memcpy(dst,src,13): one exact 13-byte F03. */
    __asm__ volatile(".globl t11_memcpy13\nt11_memcpy13:\n");
    memcpy(g_dst, g_src, 13);

    /* Overlapping memmove(buf+8, buf, 16): one exact F03. */
    __asm__ volatile(".globl t11_memmove_overlap\nt11_memmove_overlap:\n");
    memmove(g_buf + 1, g_buf, 16);

    /* strcpy(dst,"abc"): one 4-byte F03 including NUL. */
    __asm__ volatile(".globl t11_strcpy_abc\nt11_strcpy_abc:\n");
    strcpy(g_str_dst, g_lit_abc);

    /* strncpy(dst,"abc",8): one 4-byte F03; full 8-byte destination
     * invalidation; no copy row for the padding. */
    __asm__ volatile(".globl t11_strncpy_pad\nt11_strncpy_pad:\n");
    strncpy(g_str_dst + 16, g_lit_abc, 8);

    /* strncpy(dst, eight_nonzero_bytes, 8): one 8-byte F03. */
    __asm__ volatile(".globl t11_strncpy_full\nt11_strncpy_full:\n");
    strncpy(g_str_dst + 32, g_lit_eight, 8);

    /* Zero-length memcpy and strncpy: no F03, no shadow mutation. */
    __asm__ volatile(".globl t11_memcpy_zero\nt11_memcpy_zero:\n");
    memcpy(g_dst, g_src, 0);
    __asm__ volatile(".globl t11_strncpy_zero\nt11_strncpy_zero:\n");
    strncpy(g_str_dst + 48, g_lit_abc, 0);

    /* memset over a tagged pointer slot: no F03; tag removed.  The
     * destination is the slot's STORAGE, not the pointer value. */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        "movq %%r12, g_pointer_slot2(%%rip)\n"
        : : : "r12", "memory");
    __asm__ volatile(".globl t11_memset_slot\nt11_memset_slot:\n");
    memset(&g_pointer_slot2, 0, 8);

    /* memcpy of one aligned tagged pointer slot: F03, destination F04,
     * relocated ADDRESS slot, and later reload F02. */
    __asm__ volatile(".globl t11_memcpy_slot\nt11_memcpy_slot:\n");
    memcpy(&g_pointer_slot2, &g_pointer_slot, 8);
    __asm__ volatile(
        ".globl t11_reload_copied_slot\n"
        "t11_reload_copied_slot:\n\t"
        "movq g_pointer_slot2(%%rip), %%r13\n\t"
        "movzbl (%%r13), %%eax\n"
        : : : "rax", "r13", "memory");

    /* Preflight-rejected copy into a protected page: no F03/F04. */
    {
        struct sigaction sa, old_sa;
        memset(&sa, 0, sizeof(sa));
        sa.sa_handler = fault_handler;
        sigemptyset(&sa.sa_mask);
        sigaction(SIGSEGV, &sa, &old_sa);
        if (mprotect(g_fault_page, sizeof(g_fault_page), PROT_READ) != 0) {
            return -1;
        }
        fault_seen = 0;
        if (sigsetjmp(fault_jmp, 1) == 0) {
            __asm__ volatile(".globl t11_memcpy_rejected\n"
                             "t11_memcpy_rejected:\n");
            memcpy(g_fault_page, g_src, 16);
        }
        if (!fault_seen) {
            return -1;
        }
        mprotect(g_fault_page, sizeof(g_fault_page),
                 PROT_READ | PROT_WRITE);
        sigaction(SIGSEGV, &old_sa, NULL);
    }

    g_sink ^= g_dst[0] ^ ((volatile uint8_t *)p)[0];
    _exit(0);
}
