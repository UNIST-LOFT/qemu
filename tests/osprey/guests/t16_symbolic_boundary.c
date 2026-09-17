/* t16_symbolic_boundary: Stage-7 symbolic boundary-advisor fixture.
 *
 * The guest reads a scalar from the injected input file, so the tracer models
 * the loaded value symbolically.  That value is then compared against a
 * constant threshold, and the observed byte sits on the "low" side, so a
 * comparison-guided advisor can propose the threshold itself and flip the
 * branch.  The guest reports which side it observed so a real mutation child
 * proves the flip end-to-end rather than merely echoing a plan value.
 *
 * The observation file is written through the path in
 * BINRADAR_SYMBOLIC_OBSERVATION_FILE; when unset the guest stays silent.  Each
 * forked child appends its own line.
 */
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* The buffer the injected input lands in.  It must be an ordinary writable
 * global so the retained read is recorded as a primitive memory access. */
static uint8_t t16_input[64];

/* The branch this fixture is built around.  `t16_check` is the entrypoint
 * symbol BinRadar is told about, so the forkserver stops handing out
 * iterations after this function has been entered the configured number of
 * times. */
int t16_check(void);

__attribute__((noinline)) int t16_check(void)
{
    /* The load must be consumed by the comparison *directly*, with no
     * intermediate spill: the advisor proposes a value for the memory cell a
     * retained read observes, and a compiler spill of that same value is
     * re-materialized by the guest before the branch, which would overwrite
     * the proposed bytes.  Reading the global in the compare keeps the
     * mutation live: the resumed child re-loads the cell and observes it. */
    const volatile uint32_t *value = (const volatile uint32_t *)t16_input;

    if (*value < 0x1000u) {
        return 0;
    }
    return 1;
}

static void t16_report(const char *tag)
{
    const char *path = getenv("BINRADAR_SYMBOLIC_OBSERVATION_FILE");
    int fd;
    char line[96];
    int length;
    uint32_t value;

    if (path == NULL || path[0] == '\0') return;
    value = *(const volatile uint32_t *)t16_input;
    fd = open(path, O_WRONLY | O_CREAT | O_APPEND, 0644);
    if (fd < 0) return;
    length = snprintf(line, sizeof(line), "[t16] [tag %s] [value %08x]\n",
                      tag, value);
    if (length > 0) {
        ssize_t written = write(fd, line, (size_t)length);
        (void)written;
    }
    close(fd);
}

static int t16_load_input(void)
{
    const char *path = getenv("SYMBOLIC_TESTCASE_NAME");
    int fd;
    ssize_t count;

    if (path == NULL || path[0] == '\0') return 0;
    fd = open(path, O_RDONLY);
    if (fd < 0) return 0;
    /* Only the first read is the symbolic injection point; the rest of the
     * buffer stays zero so the loaded scalar is the input's first bytes. */
    count = read(fd, t16_input, 4);
    close(fd);
    return count > 0;
}

int main(void)
{
    if (!t16_load_input()) {
        _exit(79);
    }
    t16_report("enter");
    if (t16_check()) {
        t16_report("high");
    } else {
        t16_report("low");
    }
    t16_report("exit");
    _exit(0);
}
