#include "binradar-forkserver.h"

#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>

int binradar_forkserver_read_exact(int fd, void *buffer, size_t length)
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

int binradar_forkserver_write_exact(int fd, const void *buffer,
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
    case BINRADAR_FORKSERVER_ATTEMPT_CAPACITY: return "capacity";
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
    case BINRADAR_FORKSERVER_STOP_CAPACITY: return "capacity";
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
    driver->replay_mode = g_strcmp0(getenv("BINRADAR_REPLAY_SERVER"), "1") == 0;
    driver->cancel_fd = -1;
    if (driver->replay_mode) {
        const char *fd = getenv("BINRADAR_REPLAY_CANCEL_FD");
        if (fd == NULL || atoi(fd) < 3) return false;
        driver->cancel_fd = atoi(fd);
        if (!binradar_forkserver_set_nonblock(driver->cancel_fd)) return false;
    }
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
    const uint32_t version = driver != NULL && driver->replay_mode
        ? BINRADAR_FORKSERVER_PROTOCOL_REPLAY : BINRADAR_FORKSERVER_PROTOCOL_V5;
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
    binradar_forkserver_begin_attempt(driver);
    return true;
}

void binradar_forkserver_begin_attempt(BinradarForkserverDriver *driver)
{
    if (driver == NULL) return;
    driver->attempt++;
    driver->next_attempt = driver->attempt + 1u;
    driver->attempt_result = BINRADAR_FORKSERVER_ATTEMPT_COMPLETED;
    driver->last_wait_result = 0;
    driver->cancel_requested = false;
    /* A cancel token is consumed by wait_child for the request it targets;
     * draining here would silently drop a cutoff that arrived before fork. */
    driver->attempt_deadline_us = binradar_forkserver_attempt_deadline();
}

bool binradar_forkserver_next_command(BinradarForkserverDriver *driver,
                                      uint32_t *command)
{
    if (driver == NULL || command == NULL) return false;
    if (binradar_forkserver_read_exact(driver->control_fd, command,
                                       sizeof(*command)) < 0) {
        return false;
    }
    uint32_t request_id;
    if (binradar_forkserver_read_exact(driver->control_fd, &request_id,
                                       sizeof(request_id)) < 0 ||
        request_id == 0 || request_id <= driver->request_id) return false;
    driver->request_id = request_id;
    if (*command == BINRADAR_REPLAY_SHUTDOWN) return true;
    if (*command != BINRADAR_REPLAY_GENERATE &&
        *command != BINRADAR_REPLAY_FINISH &&
        *command != BINRADAR_REPLAY_CASE &&
        *command != BINRADAR_REPLAY_LIST &&
        *command != BINRADAR_REPLAY_VALIDATE) return false;
    driver->cancel_requested = false;
    return true;
}

bool binradar_forkserver_replay_case_request(BinradarForkserverDriver *driver,
                                             uint32_t *mutation,
                                             char **descriptor)
{
    uint32_t length = 0;
    if (driver == NULL || mutation == NULL || descriptor == NULL) return false;
    if (binradar_forkserver_read_exact(driver->control_fd, mutation,
                                       sizeof(*mutation)) < 0 ||
        binradar_forkserver_read_exact(driver->control_fd, &length,
                                       sizeof(length)) < 0) {
        return false;
    }
    if (length > BRCACHE_MAX_DESCRIPTOR) return false;
    char *text = g_malloc0((gsize)length + 1u);
    if (length > 0 &&
        binradar_forkserver_read_exact(driver->control_fd, text, length) < 0) {
        g_free(text);
        return false;
    }
    text[length] = '\0';
    *descriptor = text;
    return true;
}

bool binradar_forkserver_send_ack(BinradarForkserverDriver *driver,
                                  uint32_t code)
{
    if (driver == NULL) return false;
    uint32_t reply[3] = {BINRADAR_REPLAY_REPLY_ACK, driver->request_id, code};
    return driver != NULL &&
           binradar_forkserver_write_exact(driver->status_fd, reply,
                                            sizeof(reply)) == 0;
}

bool binradar_forkserver_send_replay_list(BinradarForkserverDriver *driver,
                                          const uint32_t *ids, uint32_t count)
{
    if (driver == NULL || (ids == NULL && count != 0)) return false;
    uint32_t header[3] = {BINRADAR_REPLAY_REPLY_LIST, driver->request_id, count};
    if (binradar_forkserver_write_exact(driver->status_fd, header,
                                         sizeof(header)) != 0) {
        return false;
    }
    return count == 0 ||
        binradar_forkserver_write_exact(driver->status_fd, ids,
                                         count * sizeof(*ids)) == 0;
}

bool binradar_forkserver_send_replay_case(BinradarForkserverDriver *driver,
                                          uint32_t source, uint32_t outcome,
                                          uint32_t reason, const char *text)
{
    const size_t length = text != NULL ? strlen(text) : 0;
    if (driver == NULL || length > BINRADAR_REPLAY_CASE_TEXT_MAX) return false;
    uint32_t header[6] = {BINRADAR_REPLAY_REPLY_CASE, driver->request_id, source, outcome,
                          reason, (uint32_t)length};
    return binradar_forkserver_write_exact(driver->status_fd, header,
                                            sizeof(header)) == 0 &&
        (length == 0 ||
         binradar_forkserver_write_exact(driver->status_fd, text, length) == 0);
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
    log_msg("[forkserver] [wait-child] [pid %d] [cache %p]\n", (int)child_pid,
            (void *)cache);
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
        if (driver->cancel_fd >= 0) {
            ssize_t cancelled = read(driver->cancel_fd,
                driver->cancel_bytes + driver->cancel_bytes_used,
                sizeof(uint32_t) - driver->cancel_bytes_used);
            if (cancelled > 0) driver->cancel_bytes_used += (size_t)cancelled;
            uint32_t cancel_id = 0;
            if (driver->cancel_bytes_used == sizeof(uint32_t)) {
                memcpy(&cancel_id, driver->cancel_bytes, sizeof(cancel_id));
                driver->cancel_bytes_used = 0;
            }
            if (cancel_id != 0 && cancel_id == driver->request_id) {
                kill(child_pid, SIGKILL);
                while (waitpid(child_pid, &status, 0) < 0) {
                    if (errno != EINTR) return -1;
                }
                if (cache != NULL) {
                    binradar_cache_drain_patch(cache);
                    binradar_cache_drain_capture(cache);
                }
                driver->cancel_requested = true;
                *status_out = (uint32_t)status;
                return 3;
            }
            if (cancelled == 0 ||
                (cancelled < 0 && errno != EINTR &&
                 errno != EAGAIN && errno != EWOULDBLOCK)) return -1;
        }
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
    if (attempt_result == BINRADAR_FORKSERVER_ATTEMPT_CAPACITY) {
        return BINRADAR_FORKSERVER_STOP_CAPACITY;
    }
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
    uint32_t summary[BINRADAR_REPLAY_SUMMARY_WORDS];
    size_t words;
    if (driver == NULL) return false;
    if (driver->replay_mode) {
        /* Bind every resident reply to its command before payload parsing. */
        summary[0] = BINRADAR_REPLAY_REPLY_SUMMARY;
        summary[1] = driver->request_id;
        summary[2] = driver->attempt;
        summary[3] = representative_runs;
        summary[4] = remaining_plans;
        summary[5] = driver->attempt_result;
        summary[6] = (uint32_t)stop_reason;
        summary[7] = driver->retained_mutations;
        words = BINRADAR_REPLAY_SUMMARY_WORDS;
    } else {
        summary[0] = driver->attempt;
        summary[1] = representative_runs;
        summary[2] = remaining_plans;
        summary[3] = driver->attempt_result;
        summary[4] = (uint32_t)stop_reason;
        words = BINRADAR_FORKSERVER_SUMMARY_WORDS;
    }
    if (binradar_forkserver_write_exact(driver->status_fd, summary,
            words * sizeof(uint32_t)) != 0) {
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
