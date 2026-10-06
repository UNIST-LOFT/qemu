/* t87: a finding published before BINRADAR_ENTRYPOINT is not a reference.
 *
 * main() runs early_fault() (a heap OOB) and only then calls entry_function(),
 * which commits a second, distinct heap OOB.  The forkserver snapshots
 * immediately before entry_function, so every child resumes there and can
 * never re-execute early_fault().  With BINRADAR_ENTRYPOINT set to
 * entry_function the reference pass must therefore
 *
 *   - report early_fault() as `[prov] [prefix-finding]`, and
 *   - publish the in-window entry_function() fault as the only identity.
 *
 * Publishing the prefix fault instead would make `same-fault` unreachable by
 * construction: no child can ever produce a PC that already happened before
 * the snapshot.  With BINRADAR_ENTRYPOINT at main (the control case) the
 * window opens before early_fault() and the prefix fault is the reference,
 * exactly as before this rule existed.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

__attribute__((noinline)) static void early_fault(void)
{
    char *p = malloc(8);
    if (p == NULL) return;
    fprintf(stderr, "[t87] [early]\n");
    __asm__ volatile(".global early_fault_pc\nearly_fault_pc:\n\t"
                     "movb $0x41, 9(%0)\n"
                     : : "r"(p) : "memory");
    free(p);
}

__attribute__((noinline)) void entry_function(void)
{
    char *q = malloc(16);
    if (q == NULL) return;
    fprintf(stderr, "[t87] [entry]\n");
    __asm__ volatile(".global entry_fault_pc\nentry_fault_pc:\n\t"
                     "movb $0x42, 17(%0)\n"
                     : : "r"(q) : "memory");
    free(q);
}

int main(void)
{
    early_fault();
    entry_function();
    return 0;
}
