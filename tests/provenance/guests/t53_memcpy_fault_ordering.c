/* Failed model preflight must not mutate shadow state or publish a finding;
 * the real memcpy load from PROT_NONE supplies the target signal. */
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

int main(void)
{
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    char *dst = malloc(32);
    void *src = mmap(NULL, page, PROT_NONE,
                     MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (!dst || src == MAP_FAILED) {
        return 106;
    }
    memcpy(dst, src, 16);
    return 107;
}
