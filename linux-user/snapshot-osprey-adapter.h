#ifndef BINRADAR_SNAPSHOT_OSPREY_ADAPTER_H
#define BINRADAR_SNAPSHOT_OSPREY_ADAPTER_H

#include "snapshot-mutation.h"

typedef struct SnapshotOspreyAdapter {
    OspreyContext *context;
    bool enabled;
    bool mutation_mode;
} SnapshotOspreyAdapter;

void snapshot_osprey_adapter_init(SnapshotOspreyAdapter *adapter,
                                  OspreyContext *context, bool enabled,
                                  bool mutation_mode);
bool snapshot_osprey_adapter_is_mutation_mode(
    const SnapshotOspreyAdapter *adapter);
bool snapshot_osprey_adapter_prepare(SnapshotOspreyAdapter *adapter);
OspreyRuntimeResolveStatus snapshot_osprey_adapter_resolve_pointer(
    SnapshotOspreyAdapter *adapter,
    const SnapshotMutationBaselineEntry *entry,
    target_ulong concrete_value,
    OspreyRuntimePointerResolution *resolution);

#endif /* BINRADAR_SNAPSHOT_OSPREY_ADAPTER_H */
