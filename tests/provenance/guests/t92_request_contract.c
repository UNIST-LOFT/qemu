#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <unistd.h>

/* All rejected payloads are protected before transfer, never dereferenced.
 * The protected page is wholly inside malloc's extent, away from its headers. */
static int request_errno;

static long request(long nr, int fd, const void *base, size_t length)
{
    long ret;
    __asm__ volatile(".global request_contract_pc\nrequest_contract_pc: syscall"
                     : "=a"(ret) : "0"(nr), "D"(fd), "S"(base), "d"(length)
                     : "rcx", "r11", "memory");
    request_errno = errno;
    return ret;
}

static void request_access(char *p)
{
    __asm__ volatile(".global request_access_pc\nrequest_access_pc: movb $65,8(%0)"
                     : : "r"(p) : "memory");
}

static void prefix_request(void)
{
    char *p = malloc(8);
    if (!p) exit(20);
    long ret;
    __asm__ volatile(".global request_prefix_pc\nrequest_prefix_pc: syscall"
                     : "=a"(ret) : "0"((long)SYS_write), "D"(-1L),
                       "S"(p), "d"(12L) : "rcx", "r11", "memory");
    if (ret != -EBADF) exit(21);
    free(p);
}

__attribute__((noinline)) void request_entry(const char *mode)
{
    char *p = malloc(8);
    if (!p) exit(22);
    if (!strcmp(mode, "access-first")) request_access(p);
    if (request(SYS_write, -1, p, 12) != -EBADF) exit(23);
    if (!strcmp(mode, "request-first")) request_access(p);
    if (!strcmp(mode, "signal")) {
        __asm__ volatile("xor %%eax,%%eax\n.global request_signal_pc\nrequest_signal_pc: ud2"
                         : : : "rax", "memory");
    }
    if (!strcmp(mode, "timeout")) for (;;) __asm__ volatile("" ::: "memory");
    free(p);
}

/* The queue visits the latest primitive read first. Keep this byte the last
 * scalar read by using raw write/exit, without errno or libc teardown reads. */
__attribute__((noreturn, noinline))
void request_reset_entry(const char *input, char *payload)
{
    __asm__ volatile("cmpb $65,(%[input])\n"
                     "jne 1f\n"
                     "mov $1,%%eax\n"
                     "mov $-1,%%rdi\n"
                     "mov $12,%%edx\n"
                     ".global request_reset_pc\nrequest_reset_pc: syscall\n"
                     "1: mov $60,%%eax\n"
                     "xor %%edi,%%edi\n"
                     "syscall"
                     : : [input] "r"(input), "S"(payload)
                     : "rax", "rdi", "rdx", "rcx", "r11", "cc", "memory");
    __builtin_unreachable();
}

int main(int argc, char **argv)
{
    if (argc != 2) return 2;
    const char *mode = argv[1];
    if (!strcmp(mode, "prefix")) {
        prefix_request();
        request_entry(mode);
        return 0;
    }
    if (!strcmp(mode, "reset")) {
        const char *path = getenv("SYMBOLIC_TESTCASE_NAME");
        char input;
        int fd = path ? open(path, O_RDONLY) : -1;
        if (fd < 0 || read(fd, &input, 1) != 1) return 24;
        close(fd);
        char *payload = malloc(8);
        if (!payload) return 25;
        request_reset_entry(&input, payload);
    }
    if (!strcmp(mode, "request-first") || !strcmp(mode, "access-first") ||
        !strcmp(mode, "signal") || !strcmp(mode, "timeout")) {
        request_entry(mode);
        return 0;
    }
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    if (page != 4096) return 3;
    size_t size = page * 4;
    char *p = malloc(size);
    if (!p) return 4;
    memset(p, 'R', size);
    char *protected = (char *)((((uintptr_t)p + page - 1) & ~(page - 1)) + page);
    int pipes[2];
    if (pipe(pipes)) return 5;
    long ret;
    errno = EDOM;
    if (!strcmp(mode, "success") || !strcmp(mode, "badfd")) {
        int badfd = !strcmp(mode, "badfd");
        ret = request(SYS_write, badfd ? -1 : pipes[1], p, 8);
        if (ret != (badfd ? -EBADF : 8)) return 6;
        if (!badfd) {
            char received[8];
            if (read(pipes[0], received, 8) != 8 || memcmp(received, "RRRRRRRR", 8)) return 7;
        }
    } else if (!strcmp(mode, "short")) {
        if (fcntl(pipes[1], F_SETPIPE_SZ, 4096) != 4096 ||
            fcntl(pipes[1], F_SETFL, O_NONBLOCK)) return 8;
        ret = request(SYS_write, pipes[1], p, 8192);
        if (ret != 4096) return 9;
        char received[4096];
        if (read(pipes[0], received, sizeof(received)) != 4096) return 10;
        for (size_t i = 0; i < sizeof(received); ++i) if (received[i] != 'R') return 11;
    } else {
        if (mprotect(protected, page, PROT_NONE)) return 12;
        int fd = pipes[1];
        if (!strcmp(mode, "null-oob")) {
            fd = open("/dev/null", O_WRONLY);
            if (fd < 0) return 13;
        }
        if (!strcmp(mode, "vector-clamp")) {
            struct iovec vec = {p, 0x7ffff001UL};
            ret = request(SYS_writev, fd, &vec, 1);
        } else if (!strcmp(mode, "later-precedence")) {
            struct iovec vec[3] = {{p, 1}, {p, size + 1}, {p, (size_t)-1}};
            ret = request(SYS_writev, fd, vec, 3);
        } else if (!strcmp(mode, "vector-oob") || !strcmp(mode, "precedence")) {
            struct iovec vec[2] = {{p, size + 1}, {p, (size_t)-1}};
            ret = request(SYS_writev, fd, vec, !strcmp(mode, "precedence") ? 2 : 1);
        } else {
            int clean = !strcmp(mode, "protected");
            ret = request(SYS_write, fd, clean ? protected : p, clean ? page : size + 1);
        }
        if (mprotect(protected, page, PROT_READ | PROT_WRITE)) return 14;
        if (fd != pipes[1]) close(fd);
        if (ret != (!strcmp(mode, "later-precedence") ? -EINVAL : -EFAULT)) return 15;
        /* The rejected transfer must leave the pipe empty (no host write). */
        int available = -1;
        if (ioctl(pipes[0], FIONREAD, &available)) return 16;
        if (available != 0) return 17;
    }
    if (request_errno != EDOM) return 18;
    printf("t92 mode=%s result=%ld errno=%d bytes=%ld\n", mode, ret, request_errno, ret > 0 ? ret : 0);
    free(p);
    close(pipes[0]);
    close(pipes[1]);
    return 0;
}
