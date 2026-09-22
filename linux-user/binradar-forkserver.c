#include "binradar-forkserver.h"

#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>

#define FORKSERVER_ABORT_DEFAULT 10

static int binradar_forkserver_read_exact(int fd, void *buffer, size_t length)
{
    uint8_t *bytes = buffer;
    size_t total = 0;
    while (total < length) {
        ssize_t count = read(fd, bytes + total, length - total);
        if (count < 0 && errno == EINTR) continue;
        if (count <= 0) return -1;
        total += (size_t)count;
    }
    return 0;
}

static int binradar_forkserver_write_exact(int fd, const void *buffer,
                                            size_t length)
{
    const uint8_t *bytes = buffer;
    size_t total = 0;
    while (total < length) {
        ssize_t count = write(fd, bytes + total, length - total);
        if (count < 0 && errno == EINTR) continue;
        if (count <= 0) return -1;
        total += (size_t)count;
    }
    return 0;
}

static int64_t binradar_forkserver_child_timeout_ms(void)
{
    const char *value = getenv("BINRADAR_FORKSERVER_CHILD_TIMEOUT");
    if (value == NULL) return -1;
    int64_t seconds = atoll(value);
    if (seconds <= 0 || seconds > INT64_MAX / 1000) return -1;
    return seconds * 1000;
}

static int64_t binradar_forkserver_iteration_deadline(void)
{
    const char *value = getenv("BINRADAR_FORKSERVER_ITERATION_TIMEOUT");
    if (value == NULL) return -1;
    int64_t seconds = atoll(value);
    if (seconds <= 0 || seconds > INT64_MAX / G_USEC_PER_SEC) return -1;
    return g_get_monotonic_time() + seconds * G_USEC_PER_SEC;
}

static bool binradar_forkserver_set_nonblock(int fd)
{
    int flags = fcntl(fd, F_GETFL);
    return flags >= 0 && fcntl(fd, F_SETFL, flags | O_NONBLOCK) == 0;
}

bool binradar_forkserver_driver_init(BinradarForkserverDriver *driver,
                                     int control_fd, int status_fd)
{
    const char *abort_text;
    if (driver == NULL || control_fd < 0 || status_fd < 0) return false;
    memset(driver, 0, sizeof(*driver));
    driver->control_fd = control_fd;
    driver->status_fd = status_fd;
    abort_text = getenv("BINRADAR_FORKSERVER_TIMEOUT_ABORT_COUNT");
    driver->abort_after_timeouts = abort_text != NULL
        ? atoi(abort_text) : FORKSERVER_ABORT_DEFAULT;
    driver->iteration_deadline_us = -1;
    return true;
}

bool binradar_forkserver_handshake(BinradarForkserverDriver *driver)
{
    const uint32_t version = BINRADAR_FORKSERVER_PROTOCOL_V3;
    const uint32_t expected = version ^ UINT32_MAX;
    uint32_t reply = 0;
    return driver != NULL &&
           binradar_forkserver_write_exact(driver->status_fd, &version,
                                            sizeof(version)) == 0 &&
           binradar_forkserver_read_exact(driver->control_fd, &reply,
                                           sizeof(reply)) == 0 &&
           reply == expected &&
           binradar_forkserver_write_exact(driver->status_fd, &version,
                                            sizeof(version)) == 0;
}

bool binradar_forkserver_next(BinradarForkserverDriver *driver,
                              uint32_t *was_killed)
{
    if (driver == NULL || was_killed == NULL ||
        binradar_forkserver_read_exact(driver->control_fd, was_killed,
                                       sizeof(*was_killed)) < 0) {
        return false;
    }
    driver->iteration++;
    driver->iteration_deadline_us =
        binradar_forkserver_iteration_deadline();
    return true;
}

int binradar_forkserver_wait_child(
    BinradarForkserverDriver *driver, pid_t child_pid,
    BinradarManager *cache, uint32_t *status_out,
    BinradarForkserverSalvage salvage, void *salvage_opaque)
{
    int status = 0;
    int64_t child_timeout_ms = binradar_forkserver_child_timeout_ms();
    int64_t child_deadline = child_timeout_ms >= 0
        ? g_get_monotonic_time() + child_timeout_ms * 1000 : -1;
    struct pollfd poll_fds[2];
    nfds_t count = 0;

    if (driver == NULL || status_out == NULL) return -1;
    if (cache != NULL) {
        if (!binradar_forkserver_set_nonblock(cache->patch_fd_r)) return -1;
        poll_fds[count++] = (struct pollfd){
            .fd = cache->patch_fd_r,
            .events = POLLIN | POLLHUP | POLLERR,
        };
        if (cache->cache_fd_r >= 0) {
            if (!binradar_forkserver_set_nonblock(cache->cache_fd_r)) {
                return -1;
            }
            poll_fds[count++] = (struct pollfd){
                .fd = cache->cache_fd_r,
                .events = POLLIN | POLLHUP | POLLERR,
            };
        }
    }

    for (;;) {
        pid_t waited = waitpid(child_pid, &status, WNOHANG);
        if (waited == child_pid) break;
        if (waited < 0) return -1;
        int64_t now = g_get_monotonic_time();
        bool iteration_timeout = driver->iteration_deadline_us >= 0 &&
                                 now >= driver->iteration_deadline_us;
        bool child_timeout = child_deadline >= 0 && now >= child_deadline;
        if (iteration_timeout || child_timeout) {
            log_msg(iteration_timeout
                    ? "[forkserver] [iteration-timeout] killing child %d\n"
                    : "[forkserver] [child-timeout] killing child %d after %ld ms\n",
                    (int)child_pid, (long)child_timeout_ms);
            kill(child_pid, SIGKILL);
            if (waitpid(child_pid, &status, 0) < 0) return -1;
            if (salvage != NULL) salvage(salvage_opaque, (uint32_t *)&status);
            if (cache != NULL) {
                binradar_cache_drain_patch(cache);
                binradar_cache_drain_capture(cache);
            }
            *status_out = (uint32_t)status;
            return iteration_timeout ? 2 : 1;
        }
        if (count == 0) {
            g_usleep(50 * 1000);
            continue;
        }
        int polled = poll(poll_fds, count, 50);
        if (polled < 0 && errno == EINTR) continue;
        if (polled < 0) return -1;
        if (polled > 0) {
            if (poll_fds[0].revents & (POLLIN | POLLHUP | POLLERR)) {
                binradar_cache_drain_patch(cache);
            }
            if (count == 2 &&
                (poll_fds[1].revents & (POLLIN | POLLHUP | POLLERR))) {
                binradar_cache_drain_capture(cache);
            }
        }
    }
    if (cache != NULL) {
        binradar_cache_drain_patch(cache);
        binradar_cache_drain_capture(cache);
    }
    *status_out = (uint32_t)status;
    return 0;
}

bool binradar_forkserver_record_wait(BinradarForkserverDriver *driver,
                                     int wait_result,
                                     uint32_t representative_runs)
{
    if (driver == NULL || wait_result < 0) return true;
    if (wait_result > 0) {
        driver->consecutive_child_timeouts++;
        log_msg("[forkserver] [child-timeout] [consecutive %d]\n",
                driver->consecutive_child_timeouts);
    } else {
        driver->consecutive_child_timeouts = 0;
    }
    if (wait_result == 2 ||
        (driver->abort_after_timeouts > 0 &&
         driver->consecutive_child_timeouts >=
             driver->abort_after_timeouts)) {
        log_msg("[forkserver] [abort] [consecutive-timeout %d] "
                "[iter %u] [runs %u]\n",
                driver->consecutive_child_timeouts, driver->iteration,
                representative_runs);
        return true;
    }
    return false;
}

bool binradar_forkserver_send_summary(BinradarForkserverDriver *driver,
                                      uint32_t representative_runs,
                                      uint32_t remaining_mods)
{
    if (driver == NULL) return false;
    const uint32_t summary[3] = {
        driver->iteration,
        representative_runs,
        remaining_mods,
    };
    return binradar_forkserver_write_exact(driver->status_fd, summary,
                                            sizeof(summary)) == 0;
}

void binradar_forkserver_child_close(const BinradarForkserverDriver *driver)
{
    if (driver == NULL) return;
    close(driver->control_fd);
    close(driver->status_fd);
}
