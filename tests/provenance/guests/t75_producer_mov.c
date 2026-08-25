/* t75: exact producer metadata for a mov transfer.
 *
 * The tag is transferred by `mov %%rbx, %%rcx` before the access, so
 * the finding's producer must be that mov: kind 4 =
 * PROV_PRODUCER_MOV, producer_pc = prov_mov_site, and the last writer
 * of the EA base register (RCX) must be the same mov.  The access is
 * the movb store at prov_access_site.  All PCs are resolved from the
 * named guest symbols by the runner, never hard-coded.
 */

int main(void) {
    __asm__ volatile(
        "mov $8, %%edi\n\t"
        "call malloc@plt\n\t"
        "test %%rax, %%rax\n\t"
        "jz 1f\n\t"
        "mov %%rax, %%rbx\n\t"
        "prov_mov_site:\n\t"
        "mov %%rbx, %%rcx\n\t"
        "prov_access_site:\n\t"
        "movb $1, 8(%%rcx)\n\t"
        "1:\n\t"
        : : : "rax", "rbx", "rcx", "rdi", "rsi", "rdx", "r8", "r9",
              "r10", "r11", "memory");
    return 0;
}
