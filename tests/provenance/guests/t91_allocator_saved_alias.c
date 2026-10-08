/* Opaque allocator execution must preserve application callee-saved register
 * and caller stack provenance. Both aliases really are stale: realloc/copy
 * internals must not erase their tags and hide this application UAF. */
#include <stdlib.h>

int main(int argc, char **argv)
{
    if (argc != 2) return 110;
    char *p = malloc(32);
    if (!p) return 111;
    register char *saved __asm__("r12") = p;
    char *volatile slot = p;
    __asm__ volatile("" : "+r"(saved) : : "memory");
    free(p);
    void *fresh = malloc(256);
    if (!fresh) return 112;
    free(fresh);
    __asm__ volatile("" : "+r"(saved) : : "memory");
    if (argv[1][0] == 'r') saved[0] = 1;
    else slot[0] = 1;
    return 0;
}
