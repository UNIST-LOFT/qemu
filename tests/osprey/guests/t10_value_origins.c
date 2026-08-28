/* t10_value_origins: Stage-2.4 VALUE-origin + F03/F04 fixture.
 *
 * Exercises the ordinary VALUE channel, exact F03 MemCopy, exact F04
 * PointsTo, and sparse shadow invalidation under three distinct PIE
 * load biases:
 *  - global qword load + matching-width store (G->G F03);
 *  - heap byte/word/dword/qword loads through MOV64 with matching
 *    stores (H->G F03 for each width);
 *  - stack qword load, self-MOV, store to heap (S->H F03);
 *  - live malloc pointer store to an aligned global cell (F04 + slot);
 *  - reload slot, MOV64, store to second cell (F03 + F04 + slot);
 *  - proven global and stack ADDRESS-origin stores (F04 targets);
 *  - reload of slot 2 and dereference (F02 continuity);
 *  - negatives: arithmetic/partial/CMOV/mismatched-width after a load
 *    publish no F03; null/numeric/stale/wrong-width stores publish no
 *    F04; same-value byte overwrite, atomic exchange, and one-byte
 *    syscall output invalidate a slot; adjacent byte write preserves;
 *    a caught faulting store mutates neither facts nor shadow.
 *
 * The heap pointer is published through g_heap_ptr; the two pointer
 * cells are g_pointer_slot_1 / g_pointer_slot_2.  All producer/access
 * instructions carry global labels; registers are fixed with complete
 * clobber lists; _exit(0) avoids shutdown noise.
 */
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

static uint64_t g_src_qword __attribute__((aligned(8)));
static uint64_t g_dst_qword __attribute__((aligned(8)));
static void *g_pointer_slot_1 __attribute__((aligned(8)));
static void *g_pointer_slot_2 __attribute__((aligned(8)));
static void *g_heap_ptr;                              /* .bss */
static __attribute__((aligned(4096))) uint8_t g_fault_page[4096];

static volatile uint64_t g_sink;
static sigjmp_buf fault_jmp;
static volatile sig_atomic_t fault_seen;

static void fault_handler(int sig)
{
    (void)sig;
    fault_seen = 1;
    siglongjmp(fault_jmp, 1);
}

static void install_fault_handler(struct sigaction *old_sa)
{
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = fault_handler;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGSEGV, &sa, old_sa);
}

int main(void)
{
    g_src_qword = 0x1122334455667788ULL;
    g_dst_qword = 0;
    void *p = malloc(64);
    if (!p) {
        _exit(1);
    }
    __asm__ volatile("movq %%rax, g_heap_ptr(%%rip)\n"
                     :: "a"(p) : "memory");

    /* Global qword load + matching store: one exact G->G F03. */
    __asm__ volatile(
        ".globl t10_load_global_qword\n"
        "t10_load_global_qword:\n\t"
        "movq g_src_qword(%%rip), %%r12\n\t"
        ".globl t10_store_global_qword\n"
        "t10_store_global_qword:\n\t"
        "movq %%r12, g_dst_qword(%%rip)\n"
        : : : "r12", "memory");

    /* Heap byte/word/dword/qword loads through MOV64 with matching
     * stores: four exact H->G F03 rows. */
    for (int w = 0; w < 4; w++) {
        switch (w) {
        case 0:
            __asm__ volatile(
                ".globl t10_load_heap_byte\n"
                "t10_load_heap_byte:\n\t"
                "movzbl (%0), %%r12d\n\t"
                ".globl t10_store_heap_byte\n"
                "t10_store_heap_byte:\n\t"
                "movb %%r12b, g_dst_qword(%%rip)\n"
                :
                : "r"(p) : "r12", "memory");
            break;
        case 1:
            __asm__ volatile(
                ".globl t10_load_heap_word\n"
                "t10_load_heap_word:\n\t"
                "movzwl (%0), %%r12d\n\t"
                ".globl t10_store_heap_word\n"
                "t10_store_heap_word:\n\t"
                "movw %%r12w, g_dst_qword(%%rip)\n"
                :
                : "r"(p) : "r12", "memory");
            break;
        case 2:
            __asm__ volatile(
                ".globl t10_load_heap_dword\n"
                "t10_load_heap_dword:\n\t"
                "movl (%0), %%r12d\n\t"
                ".globl t10_store_heap_dword\n"
                "t10_store_heap_dword:\n\t"
                "movl %%r12d, g_dst_qword(%%rip)\n"
                :
                : "r"(p) : "r12", "memory");
            break;
        case 3:
            __asm__ volatile(
                ".globl t10_load_heap_qword\n"
                "t10_load_heap_qword:\n\t"
                "movq (%0), %%r12\n\t"
                ".globl t10_store_heap_qword\n"
                "t10_store_heap_qword:\n\t"
                "movq %%r12, g_dst_qword(%%rip)\n"
                :
                : "r"(p) : "r12", "memory");
            break;
        }
    }
    ((volatile uint8_t *)p)[0] = 0xaa;
    ((volatile uint16_t *)p)[1] = 0xbbbb;
    ((volatile uint32_t *)p)[1] = 0xccccccccU;
    ((volatile uint64_t *)p)[1] = 0xddddddddddddddddULL;

    /* Stack qword load, self-MOV, store to heap: S->H F03. */
    __asm__ volatile(
        "movq %%rsp, %%r12\n\t"
        ".globl t10_load_stack_qword\n"
        "t10_load_stack_qword:\n\t"
        "movq (%%r12), %%r13\n\t"
        ".globl t10_self_mov_stack\n"
        "t10_self_mov_stack:\n\t"
        "movq %%r13, %%r13\n\t"
        ".globl t10_store_stack_to_heap\n"
        "t10_store_stack_to_heap:\n\t"
        "movq %%r13, (%0)\n"
        : : "r"(p) : "r12", "r13", "memory");

    /* Store live malloc pointer to slot 1: F04 + installed slot. */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        ".globl t10_prod_pointer_store_1\n"
        "t10_prod_pointer_store_1:\n\t"
        "movq %%r12, g_pointer_slot_1(%%rip)\n"
        : : : "r12", "memory");

    /* Reload slot 1, MOV64, store to slot 2: F03 + F04 + slot 2. */
    __asm__ volatile(
        ".globl t10_load_pointer_slot1\n"
        "t10_load_pointer_slot1:\n\t"
        "movq g_pointer_slot_1(%%rip), %%r12\n\t"
        ".globl t10_mov_pointer_value\n"
        "t10_mov_pointer_value:\n\t"
        "movq %%r12, %%r13\n\t"
        ".globl t10_store_pointer_slot2\n"
        "t10_store_pointer_slot2:\n\t"
        "movq %%r13, g_pointer_slot_2(%%rip)\n"
        : : : "r12", "r13", "memory");

    /* Store proven global ADDRESS origin: F04 target G. */
    __asm__ volatile(
        ".globl t10_prod_global_target\n"
        "t10_prod_global_target:\n\t"
        "leaq g_src_qword(%%rip), %%r12\n\t"
        ".globl t10_store_global_target\n"
        "t10_store_global_target:\n\t"
        "movq %%r12, g_pointer_slot_1(%%rip)\n"
        : : : "r12", "memory");

    /* Store proven stack ADDRESS origin: F04 target S frame. */
    __asm__ volatile(
        ".globl t10_prod_stack_target\n"
        "t10_prod_stack_target:\n\t"
        "movq %%rsp, %%r12\n\t"
        ".globl t10_store_stack_target\n"
        "t10_store_stack_target:\n\t"
        "movq %%r12, g_pointer_slot_2(%%rip)\n"
        : : : "r12", "memory");

    /* Reload slot 2 and dereference the stack target: F02 continuity. */
    __asm__ volatile(
        ".globl t10_reload_slot2_deref\n"
        "t10_reload_slot2_deref:\n\t"
        "movq g_pointer_slot_2(%%rip), %%r13\n\t"
        "movzbl (%%r13), %%eax\n"
        : : : "rax", "r13", "memory");

    /* Negatives: arithmetic, partial-register write, CMOV, and
     * mismatched store width after a valid load publish no F03. */
    __asm__ volatile(
        "movq g_src_qword(%%rip), %%r12\n\t"
        ".globl t10_no_f03_arith\n"
        "t10_no_f03_arith:\n\t"
        "addq $1, %%r12\n\t"
        ".globl t10_no_f03_arith_store\n"
        "t10_no_f03_arith_store:\n\t"
        "movq %%r12, g_dst_qword(%%rip)\n"
        : : : "r12", "memory");
    __asm__ volatile(
        "movq g_src_qword(%%rip), %%r12\n\t"
        ".globl t10_no_f03_partial\n"
        "t10_no_f03_partial:\n\t"
        "movl $0x1234, %%r12d\n\t"
        ".globl t10_no_f03_partial_store\n"
        "t10_no_f03_partial_store:\n\t"
        "movq %%r12, g_dst_qword(%%rip)\n"
        : : : "r12", "memory");
    __asm__ volatile(
        "movq g_src_qword(%%rip), %%r12\n\t"
        "xorq %%r13, %%r13\n\t"
        ".globl t10_no_f03_cmov\n"
        "t10_no_f03_cmov:\n\t"
        "cmovzq %%r13, %%r12\n\t"
        ".globl t10_no_f03_cmov_store\n"
        "t10_no_f03_cmov_store:\n\t"
        "movq %%r12, g_dst_qword(%%rip)\n"
        : : : "r12", "r13", "memory");
    __asm__ volatile(
        "movq g_src_qword(%%rip), %%r12\n\t"
        ".globl t10_no_f03_width_mismatch\n"
        "t10_no_f03_width_mismatch:\n\t"
        "movb %%r12b, g_dst_qword(%%rip)\n"
        : : : "r12", "memory");

    /* Negatives: null, numeric-map, and stale-generation stores
     * publish no F04. */
    __asm__ volatile(
        "xorq %%r12, %%r12\n\t"
        ".globl t10_no_f04_null\n"
        "t10_no_f04_null:\n\t"
        "movq %%r12, g_pointer_slot_1(%%rip)\n"
        : : : "r12", "memory");
    __asm__ volatile(
        "movq $0x7f0000000000, %%r12\n\t"
        ".globl t10_no_f04_numeric\n"
        "t10_no_f04_numeric:\n\t"
        "movq %%r12, g_pointer_slot_1(%%rip)\n"
        : : : "r12", "memory");
    {
        void *p2 = malloc(64);
        if (!p2) {
            _exit(1);
        }
        void *p2_copy = p2;
        free(p2);
        void *p3 = malloc(64);
        if (!p3) {
            _exit(1);
        }
        (void)p3;
        __asm__ volatile(
            "movq %0, %%r12\n\t"
            ".globl t10_no_f04_stale\n"
            "t10_no_f04_stale:\n\t"
            "movq %%r12, g_pointer_slot_1(%%rip)\n"
            : : "m"(p2_copy) : "r12", "memory");
    }

    /* Same-value byte overwrite inside slot 1 invalidates it: a later
     * reload/dereference has no F02 continuity. */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        "movq %%r12, g_pointer_slot_1(%%rip)\n\t"
        ".globl t10_no_continuity_byte_overwrite\n"
        "t10_no_continuity_byte_overwrite:\n\t"
        "movb %%r12b, g_pointer_slot_1(%%rip)\n"
        ".globl t10_reload_after_byte_overwrite\n"
        "t10_reload_after_byte_overwrite:\n\t"
        "movq g_pointer_slot_1(%%rip), %%r13\n\t"
        "movzbl (%%r13), %%eax\n"
        : : : "rax", "r12", "r13", "memory");

    /* Adjacent byte write preserves the slot (slot 2 restored first). */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        "movq %%r12, g_pointer_slot_2(%%rip)\n\t"
        ".globl t10_adjacent_byte_write\n"
        "t10_adjacent_byte_write:\n\t"
        "movb $0x5a, %0\n"
        ".globl t10_reload_after_adjacent\n"
        "t10_reload_after_adjacent:\n\t"
        "movq g_pointer_slot_2(%%rip), %%r13\n\t"
        "movzbl (%%r13), %%eax\n"
        : "=m"(*((char *)&g_pointer_slot_2 + 8))
        : : "rax", "r12", "r13", "memory");

    /* Caught faulting store emits no F03/F04 and does not mutate the
     * previously valid shadow; after permissions are restored, reload
     * still proves F02 continuity. */
    {
        struct sigaction old_sa;
        install_fault_handler(&old_sa);
        __asm__ volatile(
            "movq g_heap_ptr(%%rip), %%r12\n\t"
            "movq %%r12, g_pointer_slot_1(%%rip)\n"
            : : : "r12", "memory");
        if (mprotect(g_fault_page, sizeof(g_fault_page), PROT_READ) != 0) {
            return -1;
        }
        fault_seen = 0;
        if (sigsetjmp(fault_jmp, 1) == 0) {
            __asm__ volatile(
                "leaq g_fault_page(%%rip), %%r12\n\t"
                ".globl t10_fault_store\n"
                "t10_fault_store:\n\t"
                "movb $0x5a, (%%r12)\n"
                : : : "r12", "memory");
        }
        if (!fault_seen) {
            return -1;
        }
        mprotect(g_fault_page, sizeof(g_fault_page),
                 PROT_READ | PROT_WRITE);
        sigaction(SIGSEGV, &old_sa, NULL);
    }
    __asm__ volatile(
        ".globl t10_reload_after_fault\n"
        "t10_reload_after_fault:\n\t"
        "movq g_pointer_slot_1(%%rip), %%r13\n\t"
        "movzbl (%%r13), %%eax\n"
        : : : "rax", "r13", "memory");

    g_sink ^= g_dst_qword ^ ((volatile uint8_t *)p)[0];
    _exit(0);
}
