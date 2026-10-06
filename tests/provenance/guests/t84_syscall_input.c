#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <unistd.h>

static long transfer(long number, int fd, const void *buf, size_t count)
{
    long result;
    register long offset_low __asm__("r10") = 0;
    register long offset_high __asm__("r8") = 0;
    __asm__ volatile(".global syscall_input_pc\nsyscall_input_pc: syscall"
                     : "=a"(result)
                     : "0"(number), "D"(fd), "S"(buf), "d"(count),
                       "r"(offset_low), "r"(offset_high)
                     : "rcx", "r11", "memory");
    return result;
}

static long libc_transfer(int fd, void *buffer, size_t count)
{
    long result;
    __asm__ volatile("call write@PLT\n.global libc_write_return\nlibc_write_return:"
                     : "=a"(result), "+D"(fd), "+S"(buffer), "+d"(count)
                     :
                     : "rcx", "r11", "r10", "r8", "r9", "cc", "memory");
    return result;
}

int main(int argc, char **argv)
{
    int pipefd[2];
    if (argc != 2 || pipe(pipefd)) return 2;
    int kind = atoi(argv[1]);
    size_t size = kind == 4 || kind == 5 ? 4096 : 8;
    char *data = malloc(size);
    if (!data) return 3;
    memset(data, 'A', size);
    long result;
    if (kind == 0) {
        result = transfer(SYS_write, pipefd[1], data, 12);
        if (result != 12) return 4;
    } else if (kind == 1) {
        result = transfer(SYS_write, -1, data, 12);
        if (result != -EBADF) return 5;
    } else if (kind == 2) {
        result = transfer(SYS_write, pipefd[1], NULL, 0);
        if (result != 0) return 6;
    } else if (kind == 3) {
        result = transfer(SYS_write, pipefd[1], (void *)1, 12);
        if (result != -EFAULT) return 7;
    } else if (kind == 6 || kind == 7 || kind == 11) {
        struct iovec vec = {data, kind == 7 ? 8 : 12};
        if (kind == 7) free(data);
        result = transfer(SYS_writev, kind == 11 ? -1 : pipefd[1], &vec, 1);
        if (kind == 7) data = NULL;
        if (result != (kind == 11 ? -EBADF : (long)vec.iov_len)) return 10;
    } else if (kind == 8) {
        struct iovec *vec = malloc(sizeof(*vec));
        if (!vec) return 11;
        vec[0] = (struct iovec){data, 8};
        result = transfer(SYS_writev, -1, vec, 2);
        free(vec);
        if (result >= 0) return 12;
    } else if (kind == 9 || kind == 10) {
        char path[] = "/tmp/binradar-syscall-XXXXXX";
        int fd = mkstemp(path);
        if (fd < 0) return 13;
        unlink(path);
        struct iovec vec = {data, 12};
        result = kind == 9 ? transfer(SYS_pwrite64, fd, data, 12)
                          : transfer(SYS_pwritev, fd, &vec, 1);
        close(fd);
        if (result != 12) return 14;
    } else if (kind == 12) {
        result = transfer(SYS_pwrite64, -1, data, 12);
        if (result != -EBADF) return 15;
    } else if (kind == 13 || kind == 14) {
        result = libc_transfer(kind == 14 ? -1 : pipefd[1], data, 12);
        if (kind == 13 && result != 12) return 16;
        if (kind == 14 && (result != -1 || errno != EBADF)) return 17;
    } else {
        if (fcntl(pipefd[1], F_SETPIPE_SZ, 4096) != 4096 ||
            fcntl(pipefd[1], F_SETFL, O_NONBLOCK)) return 8;
        if (kind == 4) {
            result = transfer(SYS_write, pipefd[1], data, 8192);
        } else {
            struct iovec vec[3] = {{data, 2048}, {NULL, 0}, {data + 2048, 4096}};
            result = transfer(SYS_writev, pipefd[1], vec, 3);
        }
        if (result != 4096) return 9;
    }
    free(data);
    close(pipefd[0]);
    close(pipefd[1]);
    return 0;
}
