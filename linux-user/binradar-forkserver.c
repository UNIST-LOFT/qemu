#include "binradar-forkserver.h"

#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>

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

const char *binradar_forkserver_attempt_result_name(uint32_t result)
{
    switch (result) {
    case BINRADAR_FORKSERVER_ATTEMPT_COMPLETED: return "completed";
    case BINRADAR_FORKSERVER_ATTEMPT_NO_OBSERVATION: return "no-observation";
    case BINRADAR_FORKSERVER_ATTEMPT_UNUSABLE_EXIT: return "unusable-exit";
    case BINRADAR_FORKSERVER_ATTEMPT_TIMEOUT: return "timeout";
    }
    return "invalid";
}

const char *binradar_forkserver_stop_reason_name(uint32_t reason)
{
    switch (reason) {
    case BINRADAR_FORKSERVER_STOP_CONTINUE: return "continue";
    case BINRADAR_FORKSERVER_STOP_EXHAUSTED: return "exhausted";
    case BINRADAR_FORKSERVER_STOP_BASELINE_UNAVAILABLE:
        return "baseline-unavailable";
    case BINRADAR_FORKSERVER_STOP_FAILURE_LIMIT: return "failure-limit";
    case BINRADAR_FORKSERVER_STOP_RESOURCE_FAILURE: return "resource-failure";
    }
    return "invalid";
}

static int64_t binradar_forkserver_child_timeout_ms(void)
{
    const char *value = getenv("BINRADAR_FORKSERVER_CHILD_TIMEOUT");
    if (value == NULL) return -1;
    int64_t seconds = atoll(value);
    if (seconds <= 0 || seconds > INT64_MAX / 1000) return -1;
    return seconds * 1000;
}

static int64_t binradar_forkserver_attempt_deadline(void)
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
    const char *limit_text;
    if (driver == NULL || control_fd < 0 || status_fd < 0) return false;
    memset(driver, 0, sizeof(*driver));
    driver->control_fd = control_fd;
    driver->status_fd = status_fd;
    /* Consecutive-bad-attempt limit.  Child timeouts and unusable exits
     * advance it; a committed attempt resets it; an ordinary no-observation
     * miss leaves it alone so a long tail of mutation misses cannot stop a
     * healthy queue. */
    limit_text = getenv("BINRADAR_FORKSERVER_TIMEOUT_ABORT_COUNT");
    driver->bad_attempt_limit = limit_text != NULL
        ? atoi(limit_text) : BINRADAR_FORKSERVER_BAD_ATTEMPT_DEFAULT;
    driver->attempt_deadline_us = -1;
    return true;
}

bool binradar_forkserver_handshake(BinradarForkserverDriver *driver)
{
    const uint32_t version = BINRADAR_FORKSERVER_PROTOCOL_V4;
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
    driver->attempt++;
    driver->next_attempt = driver->attempt + 1u;
    driver->attempt_result = BINRADAR_FORKSERVER_ATTEMPT_COMPLETED;
    driver->last_wait_result = 0;
    driver->attempt_deadline_us = binradar_forkserver_attempt_deadline();
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
        bool attempt_timeout = driver->attempt_deadline_us >= 0 &&
                               now >= driver->attempt_deadline_us;
        bool child_timeout = child_deadline >= 0 && now >= child_deadline;
        if (attempt_timeout || child_timeout) {
            log_msg(attempt_timeout
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
            return attempt_timeout ? 2 : 1;
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

BinradarForkserverStopReason binradar_forkserver_stop_reason(
    BinradarForkserverDriver *driver,
    BinradarForkserverAttemptResult attempt_result, bool discarded,
    bool deadline_kill, bool engine_failure, bool baseline_attempt,
    uint32_t remaining_plans)
{
    if (driver == NULL) return BINRADAR_FORKSERVER_STOP_EXHAUSTED;
    driver->attempt_result = (uint32_t)attempt_result;
    if (attempt_result == BINRADAR_FORKSERVER_ATTEMPT_COMPLETED &&
        !deadline_kill) {
        driver->consecutive_bad_attempts = 0;
    } else if (deadline_kill ||
               (discarded && attempt_result !=
                    BINRADAR_FORKSERVER_ATTEMPT_NO_OBSERVATION)) {
        driver->consecutive_bad_attempts++;
    }
    if (engine_failure) {
        log_msg("[forkserver] [resource-failure] [attempt %u] "
                "[consecutive-bad %d] [remaining %u]\n", driver->attempt,
                driver->consecutive_bad_attempts, remaining_plans);
        return BINRADAR_FORKSERVER_STOP_RESOURCE_FAILURE;
    }
    if (baseline_attempt && discarded) {
        log_msg("[forkserver] [baseline-unavailable] [attempt %u] "
                "[result %s] [remaining %u]\n", driver->attempt,
                binradar_forkserver_attempt_result_name(attempt_result),
                remaining_plans);
        return BINRADAR_FORKSERVER_STOP_BASELINE_UNAVAILABLE;
    }
    if (driver->bad_attempt_limit > 0 &&
        driver->consecutive_bad_attempts >= driver->bad_attempt_limit) {
        log_msg("[forkserver] [failure-limit] [consecutive-bad %d] "
                "[attempt %u] [remaining %u]\n",
                driver->consecutive_bad_attempts, driver->attempt,
                remaining_plans);
        return BINRADAR_FORKSERVER_STOP_FAILURE_LIMIT;
    }
    return remaining_plans > 0 ? BINRADAR_FORKSERVER_STOP_CONTINUE
                              : BINRADAR_FORKSERVER_STOP_EXHAUSTED;
}

bool binradar_forkserver_send_summary(
    BinradarForkserverDriver *driver, uint32_t representative_runs,
    uint32_t remaining_plans, BinradarForkserverStopReason stop_reason)
{
    uint32_t summary[BINRADAR_FORKSERVER_SUMMARY_WORDS];
    if (driver == NULL) return false;
    summary[0] = driver->attempt;
    summary[1] = representative_runs;
    summary[2] = remaining_plans;
    summary[3] = driver->attempt_result;
    summary[4] = (uint32_t)stop_reason;
    if (binradar_forkserver_write_exact(driver->status_fd, summary,
                                         sizeof(summary)) != 0) {
        return false;
    }
    log_msg("[forkserver] [summary] [attempt %u] [runs %u] "
            "[remaining %u] [result %s] [stop %s]\n", driver->attempt,
            representative_runs, remaining_plans,
            binradar_forkserver_attempt_result_name(driver->attempt_result),
            binradar_forkserver_stop_reason_name((uint32_t)stop_reason));
    return true;
}

void binradar_forkserver_child_close(const BinradarForkserverDriver *driver)
{
    if (driver == NULL) return;
    close(driver->control_fd);
    close(driver->status_fd);
}
