#ifndef BINRADAR_FORKSERVER_H
#define BINRADAR_FORKSERVER_H

#include "binradar-cache.h"

/* Protocol v5.  The handshake word changes so an old live peer fails before
 * interpreting packet bytes, and each request is answered with a fixed
 * five-word summary:
 *
 *     (attempt_id, representative_runs, remaining_plans, attempt_result,
 *      stop_reason)
 *
 * attempt_result and stop_reason are one shared enum table, mirrored by
 * ``binradar/binradar_runtime.py`` and pinned by
 * ``tests/test_binradar_forkserver_protocol.py`` against this header.
 *
 * An attempt is one complete logical sweep: the patch-0 baseline sub-run plus
 * every configured candidate that ran.  Attempt ids are strictly increasing;
 * a discarded attempt commits nothing, so evidence files may carry gaps.
 * remaining_plans is the number of mutation plans that have not been executed
 * yet, including the plan popped for the next attempt. */
#define BINRADAR_FORKSERVER_PROTOCOL_V5 0x41464c04u
/* Resident patch-zero mode has an independent command protocol so generation
 * completion and service termination are distinct.  Ordinary
 * directed/binradar peers retain v5 and its five-word summary.
 *
 * Every command starts with command, nonzero increasing request_id.
 * Request payload on the control pipe:
 *
 *     GENERATE              - run one generation attempt
 *     FINISH                - generation is over; enter the ready state
 *     CASE    id, len, text - run one retained mutation with this descriptor
 *     SHUTDOWN              - acknowledge and exit 0
 *     LIST                  - report the retained mutation ids
 *     VALIDATE 0, len, text - validate only, ACK 0 valid / 1 invalid
 *
 * Reply on the status pipe starts with reply-kind, request_id:
 *
 *     1 SUMMARY: attempt, representative_runs, remaining_plans,
 *                attempt_result, stop_reason, retained_mutations
 *     2 ACK:     code
 *     3 CASE:    source, outcome, reason, text_length, text
 *     4 LIST:    count, count * mutation_id
 */
#define BINRADAR_FORKSERVER_PROTOCOL_REPLAY 0x41464c06u
#define BINRADAR_REPLAY_GENERATE 0u
#define BINRADAR_REPLAY_FINISH 1u
#define BINRADAR_REPLAY_CASE 2u
#define BINRADAR_REPLAY_SHUTDOWN 3u
#define BINRADAR_REPLAY_LIST 4u
#define BINRADAR_REPLAY_VALIDATE 5u
#define BINRADAR_REPLAY_REPLY_SUMMARY 1u
#define BINRADAR_REPLAY_REPLY_ACK 2u
#define BINRADAR_REPLAY_REPLY_CASE 3u
#define BINRADAR_REPLAY_REPLY_LIST 4u
#define BINRADAR_FORKSERVER_SUMMARY_WORDS 5u
/* kind, request_id, attempt, representative_runs, remaining_plans, attempt_result,
 * stop_reason, retained_mutations */
#define BINRADAR_REPLAY_SUMMARY_WORDS 8u
#define BINRADAR_FORKSERVER_BAD_ATTEMPT_DEFAULT 10

typedef enum BinradarForkserverAttemptResult {
    /* Every requested child ran and the attempt produced a complete sweep. */
    BINRADAR_FORKSERVER_ATTEMPT_COMPLETED = 0,
    /* Patch 0 did not reach the patch site: an ordinary mutation miss, not an
     * engine failure.  The attempt is discarded without fabricating an empty
     * branch vector. */
    BINRADAR_FORKSERVER_ATTEMPT_NO_OBSERVATION = 1,
    /* A child ended without publishing a valid, complete exit record. */
    BINRADAR_FORKSERVER_ATTEMPT_UNUSABLE_EXIT = 2,
    /* The child or aggregate attempt deadline killed the child. */
    BINRADAR_FORKSERVER_ATTEMPT_TIMEOUT = 3,
    /* Collection stopped at a pool boundary; no complete outcome exists. */
    BINRADAR_FORKSERVER_ATTEMPT_CAPACITY = 4,
} BinradarForkserverAttemptResult;

typedef enum BinradarForkserverStopReason {
    /* The next plan is owned; the orchestrator must send another request. */
    BINRADAR_FORKSERVER_STOP_CONTINUE = 0,
    /* The finite plan queue drained; the reply is terminal. */
    BINRADAR_FORKSERVER_STOP_EXHAUSTED = 1,
    /* The initial unmutated baseline is unusable: no sound mutation source
     * exists.  No plan queue was built. */
    BINRADAR_FORKSERVER_STOP_BASELINE_UNAVAILABLE = 2,
    /* The bounded consecutive-bad-attempt counter was reached. */
    BINRADAR_FORKSERVER_STOP_FAILURE_LIMIT = 3,
    /* A child died from an unexplained host signal without publishing: the
     * engine is broken and must not be forked into again. */
    BINRADAR_FORKSERVER_STOP_RESOURCE_FAILURE = 4,
    /* Incomplete collection: discard this attempt and never sweep again. */
    BINRADAR_FORKSERVER_STOP_CAPACITY = 5,
} BinradarForkserverStopReason;

typedef struct BinradarForkserverDriver {
    int control_fd;
    int status_fd;
    int cancel_fd;
    bool replay_mode;
    uint32_t request_id;
    uint8_t cancel_bytes[sizeof(uint32_t)];
    size_t cancel_bytes_used;
    /* Set when a cancellation token killed the child of the current child
     * wait.  Cleared by the attempt/replay owner. */
    bool cancel_requested;
    uint32_t retained_mutations;
    /* Attempt id reported for the attempt being run. */
    uint32_t attempt;
    /* Attempt id published for the attempt after this one. */
    uint32_t next_attempt;
    uint32_t attempt_result;
    uint32_t last_wait_result;
    int consecutive_bad_attempts;
    int bad_attempt_limit;
    int64_t attempt_deadline_us;
} BinradarForkserverDriver;

typedef bool (*BinradarForkserverSalvage)(void *opaque,
                                          uint32_t *status_out);

int binradar_forkserver_read_exact(int fd, void *buffer, size_t length);
int binradar_forkserver_write_exact(int fd, const void *buffer, size_t length);
const char *binradar_forkserver_attempt_result_name(uint32_t result);
const char *binradar_forkserver_stop_reason_name(uint32_t reason);

bool binradar_forkserver_driver_init(BinradarForkserverDriver *driver,
                                     int control_fd, int status_fd);
bool binradar_forkserver_handshake(BinradarForkserverDriver *driver);
bool binradar_forkserver_next(BinradarForkserverDriver *driver,
                              uint32_t *was_killed);
/* Start the next generation attempt without reading a command word. */
void binradar_forkserver_begin_attempt(BinradarForkserverDriver *driver);
/* Resident-mode command framing. Every reply starts with kind, request_id.
 * Cancellation carries a uint32 request_id, never an unscoped byte. */
bool binradar_forkserver_next_command(BinradarForkserverDriver *driver,
                                      uint32_t *command);
bool binradar_forkserver_replay_case_request(BinradarForkserverDriver *driver,
                                             uint32_t *mutation,
                                             char **descriptor);
bool binradar_forkserver_send_ack(BinradarForkserverDriver *driver,
                                  uint32_t code);
bool binradar_forkserver_send_replay_list(BinradarForkserverDriver *driver,
                                          const uint32_t *ids, uint32_t count);
bool binradar_forkserver_send_replay_case(BinradarForkserverDriver *driver,
                                          uint32_t source, uint32_t outcome,
                                          uint32_t reason, const char *text);
/* Reap or kill one representative child and drain both evidence channels.
 * Returns 0 reaped, 1 child/2 aggregate attempt timeout, <0 wait failure. */
int binradar_forkserver_wait_child(
    BinradarForkserverDriver *driver, pid_t child_pid,
    BinradarManager *cache, uint32_t *status_out,
    BinradarForkserverSalvage salvage, void *salvage_opaque);
/* Record one attempt outcome in the consecutive-bad-attempt accounting and
 * derive the stop reason for the reply.
 *
 * The counter bounds the real cost of an unhealthy engine: it advances when
 * the attempt was discarded (no-observation misses excepted: they are ordinary
 * mutation misses and are cheap) and when a deadline killed a child, because
 * one deadline kill costs a whole child/attempt budget.  It resets only after
 * a usable completed attempt that no deadline interrupted.  engine_failure
 * marks an unexplained host death of the engine itself. */
BinradarForkserverStopReason binradar_forkserver_stop_reason(
    BinradarForkserverDriver *driver,
    BinradarForkserverAttemptResult attempt_result, bool discarded,
    bool deadline_kill, bool engine_failure, bool baseline_attempt,
    uint32_t remaining_plans);
bool binradar_forkserver_send_summary(
    BinradarForkserverDriver *driver, uint32_t representative_runs,
    uint32_t remaining_plans, BinradarForkserverStopReason stop_reason);
void binradar_forkserver_child_close(const BinradarForkserverDriver *driver);

#endif /* BINRADAR_FORKSERVER_H */
