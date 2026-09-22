#include "snapshot-osprey-adapter.h"

void snapshot_osprey_adapter_init(SnapshotOspreyAdapter *adapter,
                                  OspreyContext *context, bool enabled,
                                  bool mutation_mode)
{
    memset(adapter, 0, sizeof(*adapter));
    adapter->context = context;
    adapter->enabled = enabled;
    adapter->mutation_mode = mutation_mode;
}

bool snapshot_osprey_adapter_is_mutation_mode(
    const SnapshotOspreyAdapter *adapter)
{
    return adapter != NULL && adapter->context != NULL &&
           adapter->enabled && adapter->mutation_mode;
}

bool snapshot_osprey_adapter_prepare(SnapshotOspreyAdapter *adapter)
{
    return adapter != NULL && adapter->context != NULL &&
           adapter->enabled &&
           osprey_runtime_mutation_prepare(adapter->context);
}

OspreyRuntimeResolveStatus snapshot_osprey_adapter_resolve_pointer(
    SnapshotOspreyAdapter *adapter,
    const SnapshotMutationBaselineEntry *entry,
    target_ulong concrete_value,
    OspreyRuntimePointerResolution *resolution)
{
    const OspreyMutationModel *model;

    if (adapter == NULL || entry == NULL || resolution == NULL ||
        !entry->typed_eligible || entry->size != sizeof(target_ulong) ||
        entry->cell.start.valid != 1 || entry->cell.size != entry->size ||
        entry->cell.start.raw != (uint64_t)entry->addr ||
        !snapshot_osprey_adapter_prepare(adapter)) {
        return OSPREY_RUNTIME_INDEX_UNAVAILABLE;
    }
    model = osprey_runtime_mutation_model(adapter->context);
    if (model == NULL) return OSPREY_RUNTIME_INDEX_UNAVAILABLE;
    return osprey_runtime_resolve_pointer(
        adapter->context, model, &entry->cell, concrete_value,
        entry->target_ref_valid ? &entry->target_ref : NULL, resolution);
}
