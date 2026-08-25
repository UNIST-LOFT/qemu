/* File-backed MAP_FIXED reuse with identical bytes must clear the old tag. */
#include <stdint.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>

int main(void) {
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    char *p = malloc(16);
    if (!p) return 60;

    char path[] = "/tmp/prov-map-reuse-XXXXXX";
    int fd = mkstemp(path);
    if (fd < 0) return 61;
    unlink(path);
    if (ftruncate(fd, (off_t)page) != 0) return 62;
    uintptr_t raw = (uintptr_t)p;
    if (write(fd, &raw, sizeof(raw)) != (ssize_t)sizeof(raw)) return 63;

    void **slot = mmap(NULL, page, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (slot == MAP_FAILED) return 64;
    *slot = p;
    void *fixed = slot;
    if (munmap(slot, page) != 0) return 65;
    slot = mmap(fixed, page, PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_FIXED, fd, 0);
    if (slot != fixed) return 66;
    if ((uintptr_t)*slot != raw) return 68;

    free(p);
    char *reloaded = *slot;
    volatile char value = reloaded[0];
    (void)value;
    if (munmap(slot, page) != 0) return 67;
    close(fd);
    return 0;
}