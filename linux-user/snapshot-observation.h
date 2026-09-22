#ifndef BINRADAR_SNAPSHOT_OBSERVATION_H
#define BINRADAR_SNAPSHOT_OBSERVATION_H

#include "snapshot-mutation.h"
#include "provenance.h"

#define SNAPSHOT_EXIT_DESC_LEN 256

typedef struct SnapshotExitInfo {
    uint32_t valid;
    uint32_t crashed;
    int32_t target_signal;
    int32_t host_signal;
    int32_t si_code;
    int32_t exit_code;
    target_ulong guest_pc;
    target_ulong guest_cs_base;
    target_ulong fault_addr;
    uintptr_t host_fault_addr;
    uint64_t guest_last_translation_block;
    int64_t query_cursor;
    int64_t expr_cursor;
    char description[SNAPSHOT_EXIT_DESC_LEN];
} SnapshotExitInfo;

typedef struct PrimitiveAccess {
    int size;
    uintptr_t addr;
    uintptr_t pc;
    uint64_t access_id;
    uint64_t run_epoch;
    Expr *expr;
    OspreyRuntimeChunkRef cell;
    uint8_t observed_read_bytes[sizeof(target_ulong)];
    uint8_t observed_read_valid;
    uint8_t root_extension;
    int64_t expr_index;
    int64_t query_index;
} PrimitiveAccess;

typedef struct PointerAccess {
    uintptr_t addr;
    uintptr_t target;
    uintptr_t pc;
    uint64_t access_id;
    uint64_t run_epoch;
    Expr *expr;
    OspreyRuntimeChunkRef cell;
    OspreyRuntimeAddressRef target_ref;
    uint8_t observed_read_bytes[sizeof(target_ulong)];
    uint8_t observed_read_valid;
    uint8_t root_extension;
    int64_t expr_index;
    int64_t query_index;
} PointerAccess;

typedef struct SharedTraceData {
    uint64_t run_epoch;
    uint32_t prim_idx;
    uint32_t ptr_idx;
    uint64_t prim_access_cnt;
    uint64_t ptr_access_cnt;
    uint32_t prim_overflow;
    uint32_t ptr_overflow;
    SnapshotExitInfo exit_info;
    PendingProvenanceFault prov_pending_fault;
    PrimitiveAccess primitives[MAX_PRIMITIVE_ACCESS];
    PointerAccess pointers[MAX_POINTER_ACCESS];
} SharedTraceData;

/* Parent-only immutable copy.  The child-writable mapping is never exposed to
 * mutation planning through this interface. */
typedef struct SnapshotObservationView {
    uint64_t run_epoch;
    uint32_t raw_primitive_count;
    uint32_t raw_pointer_count;
    uint32_t primitive_count;
    uint32_t pointer_count;
    bool counts_valid;
    uint32_t primitive_overflow;
    uint32_t pointer_overflow;
    SnapshotExitInfo exit_info;
    PrimitiveAccess *primitives;
    PointerAccess *pointers;
} SnapshotObservationView;

SharedTraceData *snapshot_observation_create_shared(void);
void snapshot_observation_destroy_shared(SharedTraceData *shared);
bool snapshot_observation_capture(const SharedTraceData *shared,
                                  SnapshotObservationView *view);
void snapshot_observation_view_clear(SnapshotObservationView *view);

#endif /* BINRADAR_SNAPSHOT_OBSERVATION_H */
