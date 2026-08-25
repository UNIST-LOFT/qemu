/* t77: exact producer metadata for a stack-reload (pop) transfer.
 *
 * The tag is reloaded from the stack shadow by `pop %%rcx`, so the
 * finding's producer must be that pop: kind 8 = PROV_PRODUCER_LOAD,
 * producer_pc = prov_pop_site, and the last writer of the EA base
 * register (RCX) must be the same pop.  The access is the movb store
 * at prov_access_site.  All PCs are resolved from the named guest
 * symbols by the runner, never hard-coded.
 */

int main(void) {
    __asm__ volatile(
        "mov $8, %%edi\n\t"
        "call malloc@plt\n\t"
        "test %%rax, %%rax\n\t"
        "jz 1f\n\t"
        "mov %%rax, %%rbx\n\t"
        "push %%rbx\n\t"
        "prov_pop_site:\n\t"
        "pop %%rcx\n\t"
        "prov_access_site:\n\t"
        "movb $1, 8(%%rcx)\n\t"
        "1:\n\t"
        : : : "rax", "rbx", "rcx", "rdi", "rsi", "rdx", "r8", "r9",
              "r10", "r11", "memory");
    return 0;
}
