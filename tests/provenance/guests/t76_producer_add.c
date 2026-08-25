/* t76: exact producer metadata for an add-immediate fold.
 *
 * The tag is folded by `addq $8, %%rbx` before the access, so the
 * finding's producer must be that add: kind 6 =
 * PROV_PRODUCER_ADD_IMM, producer_pc = prov_add_site, and the last
 * writer of the EA base register (RBX) must be the same add.  The
 * access is the movb store at prov_access_site with tracked offset 8.
 * All PCs are resolved from the named guest symbols by the runner,
 * never hard-coded.
 */

int main(void) {
    __asm__ volatile(
        "mov $8, %%edi\n\t"
        "call malloc@plt\n\t"
        "test %%rax, %%rax\n\t"
        "jz 1f\n\t"
        "mov %%rax, %%rbx\n\t"
        "prov_add_site:\n\t"
        "addq $8, %%rbx\n\t"
        "prov_access_site:\n\t"
        "movb $1, (%%rbx)\n\t"
        "1:\n\t"
        : : : "rax", "rbx", "rdi", "rcx", "rdx", "rsi", "r8", "r9",
              "r10", "r11", "memory");
    return 0;
}
