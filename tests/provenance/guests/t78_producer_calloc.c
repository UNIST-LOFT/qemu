/* t78: exact producer metadata for a calloc-return tag.
 *
 * The pointer is used directly from the allocator return register (RAX)
 * with no intervening transfer, so the finding's producer must be the
 * calloc return hook: kind 2 = PROV_PRODUCER_CALLOC_RETURN,
 * producer_pc = the call return address (prov_alloc_site), and the last
 * writer of the EA base register must be that same return address.
 * The access is the movb store at prov_access_site with EA base RAX.
 * All PCs are resolved from the named guest symbols by the runner,
 * never hard-coded.
 */

int main(void) {
    __asm__ volatile(
        "mov $1, %%edi\n\t"
        "mov $8, %%esi\n\t"
        "call calloc@plt\n\t"
        "prov_alloc_site:\n\t"
        "test %%rax, %%rax\n\t"
        "jz 1f\n\t"
        "prov_access_site:\n\t"
        "movb $1, 8(%%rax)\n\t"
        "1:\n\t"
        : : : "rax", "rdi", "rsi", "rcx", "rdx", "r8", "r9", "r10",
              "r11", "memory");
    return 0;
}
