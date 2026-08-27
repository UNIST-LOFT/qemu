/* t09_address_origins: Stage-2.3 address-origin + F02 fixture.
 *
 * Exercises every accepted Stage-2.3 producer and its F02 BaseAddr
 * evidence under three distinct PIE load biases:
 *  - RIP-relative global materialization (leaq g_data(%rip));
 *  - precise stack MOV (movq %rsp, %r12) with the current frame;
 *  - heap MOV, tagged spill/reload through a global pointer slot,
 *    constant-offset LEA, ADD/SUB immediate, one-origin register ADD,
 *    full-width XCHG, base+untagged-index, index-only, and the
 *    self-overwriting-load pre-access snapshot;
 *  - negative access labels that must keep F01 but emit no F02
 *    (scaled index, indexed LEA, stale heap identity, SIMD round-trip)
 *    or neither (segment override, faulting store).
 *
 * The heap pointer is published to g_heap_ptr with an explicit
 * RIP-relative store from RAX (the allocator-seeded register), so every
 * later in-block `movq g_heap_ptr(%rip), %rN` is an exact aligned
 * pointer-width reload that restores the origin with the reload PC as
 * producer.  All producer/access instructions carry global labels;
 * registers are fixed with complete clobber lists; _exit(0) avoids
 * shutdown noise.
 */
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

static int g_data[4] = { 1, 2, 3, 4 };               /* .data */
static void *g_pointer_slot __attribute__((aligned(8)));
static void *g_heap_ptr;                             /* .bss */
static void *g_heap_ptr2;
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

int main(void)
{
    /* One live malloc(64) object; publish the allocator-seeded pointer
     * through a RIP-relative store so the in-block reloads restore the
     * heap origin from the aligned shadow. */
    void *p = malloc(64);
    if (!p) {
        _exit(1);
    }
    __asm__ volatile("movq %%rax, g_heap_ptr(%%rip)\n"
                     :: "a"(p) : "memory");

    /* G origin via RIP-relative LEA. */
    __asm__ volatile(
        ".globl t09_prod_global_rip\n"
        "t09_prod_global_rip:\n\t"
        "leaq g_data(%%rip), %%r12\n\t"
        ".globl t09_access_global_rip\n"
        "t09_access_global_rip:\n\t"
        "movq (%%r12), %%rax\n"
        : : : "rax", "r12", "memory");
    g_sink ^= (uint64_t)g_data[0];

    /* Precise stack MOV: RSP carries the current frame's origin. */
    __asm__ volatile(
        ".globl t09_prod_stack_mov\n"
        "t09_prod_stack_mov:\n\t"
        "movq %%rsp, %%r12\n\t"
        ".globl t09_access_stack_mov\n"
        "t09_access_stack_mov:\n\t"
        "movq (%%r12), %%rax\n"
        : : : "rax", "r12", "memory");

    /* Heap MOV: full-width reload of the live malloc pointer. */
    __asm__ volatile(
        ".globl t09_prod_heap_mov\n"
        "t09_prod_heap_mov:\n\t"
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        ".globl t09_access_heap_mov\n"
        "t09_access_heap_mov:\n\t"
        "movzbl (%%r12), %%eax\n"
        : : : "rax", "r12", "memory");

    /* Full-width self-MOV must preserve the pre-write channel until the
     * shared transfer helper refreshes its producer PC. */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        ".globl t09_prod_heap_self_mov\n"
        "t09_prod_heap_self_mov:\n\t"
        "movq %%r12, %%r12\n\t"
        ".globl t09_access_heap_self_mov\n"
        "t09_access_heap_self_mov:\n\t"
        "movzbl (%%r12), %%eax\n"
        : : : "rax", "r12", "memory");

    /* In-place constant LEA needs the pre-write base value, not the
     * post-write destination value. */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        ".globl t09_prod_heap_self_lea\n"
        "t09_prod_heap_self_lea:\n\t"
        "leaq 4(%%r12), %%r12\n\t"
        ".globl t09_access_heap_self_lea\n"
        "t09_access_heap_self_lea:\n\t"
        "movzbl (%%r12), %%eax\n"
        : : : "rax", "r12", "memory");

    /* Tagged store to g_pointer_slot, then a labeled reload. */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%rax\n\t"
        "movq %%rax, g_pointer_slot(%%rip)\n"
        : : : "rax", "memory");
    __asm__ volatile(
        ".globl t09_prod_heap_reload\n"
        "t09_prod_heap_reload:\n\t"
        "movq g_pointer_slot(%%rip), %%r13\n\t"
        ".globl t09_access_heap_reload\n"
        "t09_access_heap_reload:\n\t"
        "movzbl (%%r13), %%eax\n"
        : : : "rax", "r13", "memory");

    /* Constant-offset LEA: H_site+8. */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        ".globl t09_prod_heap_lea\n"
        "t09_prod_heap_lea:\n\t"
        "leaq 8(%%r12), %%r13\n\t"
        ".globl t09_access_heap_lea\n"
        "t09_access_heap_lea:\n\t"
        "movzbl (%%r13), %%eax\n"
        : : : "rax", "r12", "r13", "memory");

    /* ADD immediate: H_site+12. */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        "leaq 8(%%r12), %%r13\n\t"
        ".globl t09_prod_heap_add_imm\n"
        "t09_prod_heap_add_imm:\n\t"
        "addq $4, %%r13\n\t"
        ".globl t09_access_heap_add_imm\n"
        "t09_access_heap_add_imm:\n\t"
        "movzbl (%%r13), %%eax\n"
        : : : "rax", "r12", "r13", "memory");

    /* SUB immediate: H_site+10. */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        "leaq 8(%%r12), %%r13\n\t"
        ".globl t09_prod_heap_sub_imm\n"
        "t09_prod_heap_sub_imm:\n\t"
        "subq $2, %%r13\n\t"
        ".globl t09_access_heap_sub_imm\n"
        "t09_access_heap_sub_imm:\n\t"
        "movzbl (%%r13), %%eax\n"
        : : : "rax", "r12", "r13", "memory");

    /* Register ADD with untagged source: H_site+11 (r13 = H+10, +1). */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        "leaq 10(%%r12), %%r13\n\t"
        "movq $1, %%r14\n\t"
        ".globl t09_prod_heap_add_reg\n"
        "t09_prod_heap_add_reg:\n\t"
        "addq %%r14, %%r13\n\t"
        ".globl t09_access_heap_add_reg\n"
        "t09_access_heap_add_reg:\n\t"
        "movzbl (%%r13), %%eax\n"
        : : : "rax", "r12", "r13", "r14", "memory");

    /* Full-width XCHG into a cleared register. */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        "leaq 8(%%r12), %%r13\n\t"
        "xorq %%r15, %%r15\n\t"
        ".globl t09_prod_heap_xchg\n"
        "t09_prod_heap_xchg:\n\t"
        "xchgq %%r13, %%r15\n\t"
        ".globl t09_access_heap_xchg\n"
        "t09_access_heap_xchg:\n\t"
        "movzbl (%%r15), %%eax\n"
        : : : "rax", "r12", "r13", "r15", "memory");

    /* Base + untagged unscaled index, then index-only. */
    __asm__ volatile(
        ".globl t09_prod_heap_index_base\n"
        "t09_prod_heap_index_base:\n\t"
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        "movq $3, %%rcx\n\t"
        ".globl t09_access_heap_base_index\n"
        "t09_access_heap_base_index:\n\t"
        "movzbl (%%r12,%%rcx,1), %%eax\n\t"
        ".globl t09_access_heap_index_only\n"
        "t09_access_heap_index_only:\n\t"
        "movq (,%%r12,1), %%rax\n"
        : : : "rax", "rcx", "r12", "memory");

    /* Self-overwriting load: F02 uses the pre-load %r12 snapshot. */
    void *p2 = malloc(64);
    if (!p2) {
        _exit(1);
    }
    __asm__ volatile("movq %%rax, g_heap_ptr2(%%rip)\n"
                     :: "a"(p2) : "memory");
    __asm__ volatile(
        "movq g_heap_ptr2(%%rip), %%rax\n\t"
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        "movq %%rax, (%%r12)\n\t"
        ".globl t09_prod_self_base\n"
        "t09_prod_self_base:\n\t"
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        ".globl t09_access_self_load\n"
        "t09_access_self_load:\n\t"
        "movq (%%r12), %%r12\n"
        : : : "rax", "r12", "memory");

    /* Negative: scaled index (untagged zero index, shift one). */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        "movq $0, %%rcx\n\t"
        ".globl t09_no_base_scaled\n"
        "t09_no_base_scaled:\n\t"
        "movzbl (%%r12,%%rcx,2), %%eax\n"
        : : : "rax", "rcx", "r12", "memory");

    /* Negative: indexed LEA result dereferenced (destination killed). */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        "movq $2, %%rcx\n\t"
        "leaq (%%r12,%%rcx,2), %%r13\n\t"
        ".globl t09_no_base_indexed_lea\n"
        "t09_no_base_indexed_lea:\n\t"
        "movzbl (%%r13), %%eax\n"
        : : : "rax", "rcx", "r12", "r13", "memory");

    /* Negative: explicit DS segment override (mode-ineligible). */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%r12\n\t"
        ".byte 0x3e\n\t"
        ".globl t09_no_base_segment\n"
        "t09_no_base_segment:\n\t"
        "movzbl (%%r12), %%eax\n"
        : : : "rax", "r12", "memory");

    /* Negative: pointer round-tripped through XMM state. */
    __asm__ volatile(
        "movq g_heap_ptr(%%rip), %%rax\n\t"
        "movq %%rax, %%xmm0\n\t"
        "movq %%xmm0, %%r13\n\t"
        ".globl t09_no_base_simd\n"
        "t09_no_base_simd:\n\t"
        "movzbl (%%r13), %%eax\n"
        : : : "rax", "r13", "xmm0", "memory");

    /* Negative: stale heap identity after deterministic same-size
     * tcache reuse.  p3_copy's stack slot keeps the OLD provenance
     * origin; the reload's liveness check rejects it. */
    void *p3 = malloc(64);
    if (!p3) {
        _exit(1);
    }
    void *p3_copy = p3;
    free(p3);
    void *p4 = malloc(64);
    if (!p4) {
        _exit(1);
    }
    (void)p4;
    __asm__ volatile(
        ".globl t09_no_base_stale\n"
        "t09_no_base_stale:\n\t"
        "movq %0, %%r12\n\t"
        "movzbl (%%r12), %%eax\n"
        : : "m"(p3_copy) : "rax", "r12", "memory");

    /* Negative: faulting store through a RIP-relative origin into a
     * read-only page; no post-success event, no F01/F02. */
    {
        struct sigaction sa;
        struct sigaction old_sa;
        memset(&sa, 0, sizeof(sa));
        sa.sa_handler = fault_handler;
        sigemptyset(&sa.sa_mask);
        if (sigaction(SIGSEGV, &sa, &old_sa) != 0 ||
            mprotect(g_fault_page, sizeof(g_fault_page), PROT_READ) != 0) {
            return -1;
        }
        fault_seen = 0;
        if (sigsetjmp(fault_jmp, 1) == 0) {
            __asm__ volatile(
                "leaq g_fault_page(%%rip), %%r12\n\t"
                ".globl t09_fault_access\n"
                "t09_fault_access:\n\t"
                "movb $0x5a, (%%r12)\n"
                : : : "r12", "memory");
        }
        if (!fault_seen) {
            return -1;
        }
        mprotect(g_fault_page, sizeof(g_fault_page), PROT_READ | PROT_WRITE);
        sigaction(SIGSEGV, &old_sa, NULL);
    }

    g_sink ^= ((volatile uint8_t *)p)[0] ^ ((volatile uint8_t *)p2)[0];
    /* _exit: no atexit handlers, no global dtors, no _fini. */
    _exit(0);
}
