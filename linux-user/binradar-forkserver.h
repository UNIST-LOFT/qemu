#ifndef BINRADAR_FORKSERVER_H
#define BINRADAR_FORKSERVER_H

#include "binradar-cache.h"

#define BINRADAR_FORKSERVER_PROTOCOL_V3 0x41464c02u

typedef struct BinradarForkserverDriver {
    int control_fd;
    int status_fd;
    uint32_t iteration;
    int consecutive_child_timeouts;
    int abort_after_timeouts;
    int64_t iteration_deadline_us;
} BinradarForkserverDriver;

typedef bool (*BinradarForkserverSalvage)(void *opaque,
                                          uint32_t *status_out);

bool binradar_forkserver_driver_init(BinradarForkserverDriver *driver,
                                     int control_fd, int status_fd);
bool binradar_forkserver_handshake(BinradarForkserverDriver *driver);
bool binradar_forkserver_next(BinradarForkserverDriver *driver,
                              uint32_t *was_killed);
int binradar_forkserver_wait_child(
    BinradarForkserverDriver *driver, pid_t child_pid,
    BinradarManager *cache, uint32_t *status_out,
    BinradarForkserverSalvage salvage, void *salvage_opaque);
bool binradar_forkserver_record_wait(BinradarForkserverDriver *driver,
                                     int wait_result,
                                     uint32_t representative_runs);
bool binradar_forkserver_send_summary(BinradarForkserverDriver *driver,
                                      uint32_t representative_runs,
                                      uint32_t remaining_mods);
void binradar_forkserver_child_close(const BinradarForkserverDriver *driver);

#endif /* BINRADAR_FORKSERVER_H */
