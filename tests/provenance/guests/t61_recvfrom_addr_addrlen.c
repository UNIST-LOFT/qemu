/* t61: recvfrom invalidates the nonempty returned sockaddr but preserves an
 * adjacent tag beyond the caller's address capacity.  Debug consistency
 * logging makes the changed in-range tag behavior-sensitive: a missing hook
 * cannot pass merely because the reload drops a concrete-value mismatch. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>

int main(void)
{
    int receiver, sender;
    char *p = malloc(16);
    struct sockaddr_un recv_addr = {0}, send_addr = {0};
    char payload[8] = "payload";
    char buf[16];
    struct {
        char addr[32];
        uint64_t outside;
    } output;
    socklen_t addrlen = sizeof(output.addr);

    if (!p) return 60;
    free(p);

    receiver = socket(AF_UNIX, SOCK_DGRAM, 0);
    sender = socket(AF_UNIX, SOCK_DGRAM, 0);
    if (receiver < 0 || sender < 0) return 61;
    recv_addr.sun_family = AF_UNIX;
    send_addr.sun_family = AF_UNIX;
    strcpy(recv_addr.sun_path, "/tmp/t61-recv.sock");
    strcpy(send_addr.sun_path, "/tmp/t61-send.sock");
    unlink(recv_addr.sun_path);
    unlink(send_addr.sun_path);
    if (bind(receiver, (struct sockaddr *)&recv_addr, sizeof(recv_addr)) != 0)
        return 62;
    if (bind(sender, (struct sockaddr *)&send_addr, sizeof(send_addr)) != 0)
        return 63;
    if (sendto(sender, payload, sizeof(payload), 0,
               (struct sockaddr *)&recv_addr, sizeof(recv_addr)) !=
        sizeof(payload))
        return 64;

    *(uint64_t *)output.addr = (uint64_t)(uintptr_t)p;
    output.outside = (uint64_t)(uintptr_t)p;
    ssize_t r = recvfrom(receiver, buf, sizeof(buf), 0,
                         (struct sockaddr *)output.addr, &addrlen);
    if (r != 8) return 62;
    if (addrlen == 0) return 65;

    volatile uint64_t changed = *(uint64_t *)output.addr;
    (void)changed;
    uint64_t y = output.outside;
    volatile char c = *(char *)(uintptr_t)y;
    (void)c;

    unlink(recv_addr.sun_path);
    unlink(send_addr.sun_path);
    return 0;
}
