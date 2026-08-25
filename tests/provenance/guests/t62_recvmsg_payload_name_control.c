/* t62: recvmsg payload, name, and control outputs.  The kernel writes
 * exactly ret payload bytes across the iovecs, the returned msg_name
 * (msg_namelen bytes), and the control data (msg_controllen bytes).
 * Tags beyond each written range must survive (UAF on reload). */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>

int main(void) {
    int a, b;
    char *p = malloc(16);
    if (!p) return 60;
    free(p);
    a = socket(AF_UNIX, SOCK_DGRAM, 0);
    b = socket(AF_UNIX, SOCK_DGRAM, 0);
    if (a < 0 || b < 0) return 61;
    struct sockaddr_un sa, sb;
    memset(&sa, 0, sizeof(sa)); sa.sun_family = AF_UNIX;
    strcpy(sa.sun_path, "/tmp/t62-recv.sock");
    memset(&sb, 0, sizeof(sb)); sb.sun_family = AF_UNIX;
    strcpy(sb.sun_path, "/tmp/t62-send.sock");
    unlink(sa.sun_path);
    unlink(sb.sun_path);
    if (bind(a, (struct sockaddr *)&sa, sizeof(sa)) != 0) return 62;
    if (bind(b, (struct sockaddr *)&sb, sizeof(sb)) != 0) return 63;

    /* sender: 8-byte payload + SCM_RIGHTS control */
    unsigned long payload = (unsigned long)p;
    struct iovec siov[1] = {{&payload, 8}};
    char sctrl[CMSG_SPACE(sizeof(int))];
    struct msghdr smsg;
    memset(&smsg, 0, sizeof(smsg));
    smsg.msg_name = &sa; smsg.msg_namelen = sizeof(sa);
    smsg.msg_iov = siov; smsg.msg_iovlen = 1;
    smsg.msg_control = sctrl; smsg.msg_controllen = sizeof(sctrl);
    struct cmsghdr *c = CMSG_FIRSTHDR(&smsg);
    c->cmsg_level = SOL_SOCKET; c->cmsg_type = SCM_RIGHTS;
    c->cmsg_len = CMSG_LEN(sizeof(int));
    memcpy(CMSG_DATA(c), &b, sizeof(int));
    if (sendmsg(b, &smsg, 0) != 8) return 64;

    /* receiver: name (40), iov (2x8), control (40) */
    struct {
        char iov0[8];
        char iov1[8];
        uint64_t slot;   /* offset 16: payload-beyond tag */
    } r;
    r.slot = (uint64_t)p;
    struct {
        char name[32];
        uint64_t slot2;  /* offset 32: name-beyond tag */
    } rn;
    rn.slot2 = (uint64_t)p;
    struct {
        char ctrl[32];
        uint64_t slot3;  /* offset 32: control-beyond tag */
    } rc;
    rc.slot3 = (uint64_t)p;
    struct iovec riov[2] = {{r.iov0, 8}, {r.iov1, 8}};
    struct msghdr rmsg;
    memset(&rmsg, 0, sizeof(rmsg));
    rmsg.msg_name = rn.name; rmsg.msg_namelen = sizeof(rn.name);
    rmsg.msg_iov = riov; rmsg.msg_iovlen = 2;
    rmsg.msg_control = rc.ctrl; rmsg.msg_controllen = sizeof(rc.ctrl);
    ssize_t rv = recvmsg(a, &rmsg, 0);
    if (rv != 8) return 65;
    if (rmsg.msg_namelen == 0 || rmsg.msg_controllen == 0) return 66;
    /* payload-beyond tag must survive (8 bytes into iov0 only) */
    uint64_t y = r.slot;
    volatile char c1 = ((char *)y)[0];   /* UAF at p+0 */
    (void)c1;
    /* name-beyond tag must survive (only msg_namelen bytes written) */
    uint64_t y2 = rn.slot2;
    volatile char c2 = ((char *)y2)[0];  /* UAF at p+0 */
    (void)c2;
    /* control-beyond tag must survive (only msg_controllen bytes written) */
    uint64_t y3 = rc.slot3;
    volatile char c3 = ((char *)y3)[0];  /* UAF at p+0 */
    (void)c3;
    return 0;
}
