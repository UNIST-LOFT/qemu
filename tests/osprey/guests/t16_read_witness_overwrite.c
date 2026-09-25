/* t16_read_witness_overwrite: B1 read-witness negative fixture.
 *
 * The guest loads a scalar from the injected input (symbolic), then
 * unconditionally stores a constant into the very cell it is about to read
 * again, and compares that second load.  The comparison therefore always sees
 * the stored constant, so no mutation of the first load can change the branch:
 * a plan may be applied and its bytes may even be observed by the first load,
 * but the load the branch actually depends on is a different one.
 *
 * The distinction matters because a plan can be applied without being
 * consumed.  The guest reports the side it really took, derived from the
 * branch outcome rather than from any mutable cell, so a child cannot report
 * the high side without genuinely taking it.
 *
 * The observation file is written through BINRADAR_SYMBOLIC_OBSERVATION_FILE;
 * unset means silent.  Each forked child appends its own line.
 */
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

/* The buffer the injected input lands in: an ordinary writable global, so the
 * retained read is recorded as a primitive memory access. */
static uint8_t t16_input[64];

/* BinRadar's entrypoint symbol: the forkserver snapshot is taken here. */
int t16_check(void);

__attribute__((noinline)) int t16_check(void)
{
    const volatile uint32_t *value = (const volatile uint32_t *)t16_input;
    uint32_t first = *value;

    /* Destroy the candidate before the load the branch depends on.  A
     * compiler cannot remove this store: the cell is volatile and the value
     * read back below is observable. */
    *(volatile uint32_t *)t16_input = 7;
    (void)first;

    return *value >= 0x1000u;
}

static void t16_report(const char *tag, uint32_t observed)
{
    const char *path = getenv("BINRADAR_SYMBOLIC_OBSERVATION_FILE");
    char line[96];
    int fd;
    int length;

    if (path == NULL || path[0] == '\0') return;
    fd = open(path, O_WRONLY | O_CREAT | O_APPEND, 0644);
    if (fd < 0) return;
    length = snprintf(line, sizeof(line), "[t16] [tag %s] [value %08x]\n",
                      tag, observed);
    if (length > 0) {
        ssize_t written = write(fd, line, (size_t)length);
        (void)written;
    }
    close(fd);
}

static int t16_load_input(void)
{
    const char *path = getenv("SYMBOLIC_TESTCASE_NAME");
    ssize_t count;
    int fd;

    if (path == NULL || path[0] == '\0') return 0;
    fd = open(path, O_RDONLY);
    if (fd < 0) return 0;
    /* Only the first read is the symbolic injection point. */
    count = read(fd, t16_input, 4);
    close(fd);
    return count > 0;
}

int main(void)
{
    int high;

    if (!t16_load_input()) {
        _exit(79);
    }
    t16_report("enter", *(const volatile uint32_t *)t16_input);
    high = t16_check();
    /* The reported value is the cell the comparison actually read, and the
     * tag is the branch outcome, so neither can be produced by a mutation
     * that the guest overwrote. */
    t16_report(high ? "high" : "low",
               *(const volatile uint32_t *)t16_input);
    _exit(0);
}
