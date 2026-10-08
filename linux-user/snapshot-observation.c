#include "snapshot-observation.h"

const char *snapshot_fault_reference_source_name(
    SnapshotFaultReferenceSource source)
{
    switch (source) {
    case SNAPSHOT_FAULT_REFERENCE_GUEST_SIGNAL:
        return "guest-signal";
    case SNAPSHOT_FAULT_REFERENCE_PROVENANCE_ACCESS:
        return "provenance-access";
    case SNAPSHOT_FAULT_REFERENCE_SYSCALL_REQUEST:
        return "syscall-request";
    case SNAPSHOT_FAULT_REFERENCE_UNAVAILABLE:
    default:
        return "unavailable";
    }
}

SnapshotFaultReferenceSource snapshot_fault_reference_source_for_finding(
    const ProvFindingRecord *finding)
{
    switch (finding->origin) {
    case PROV_FINDING_ORIGIN_ACCESS:
        return SNAPSHOT_FAULT_REFERENCE_PROVENANCE_ACCESS;
    case PROV_FINDING_ORIGIN_SYSCALL_REQUEST:
        return SNAPSHOT_FAULT_REFERENCE_SYSCALL_REQUEST;
    default:
        return SNAPSHOT_FAULT_REFERENCE_UNAVAILABLE;
    }
}

void snapshot_exit_info_set_fault_reference(
    SnapshotExitInfo *info, SnapshotFaultReferenceSource source,
    target_ulong address, const ProvenanceFaultSite *site)
{
    bool valid = source == SNAPSHOT_FAULT_REFERENCE_GUEST_SIGNAL ||
                 source == SNAPSHOT_FAULT_REFERENCE_PROVENANCE_ACCESS ||
                 source == SNAPSHOT_FAULT_REFERENCE_SYSCALL_REQUEST;
    if (info == NULL) return;
    info->fault_site = valid && site != NULL
        ? *site : (ProvenanceFaultSite){0};
    info->fault_reference_source = valid
        ? source : SNAPSHOT_FAULT_REFERENCE_UNAVAILABLE;
    /* A zero address is meaningful only for an explicitly valid reference.
     * Unavailable observations use zero as their stable placeholder. */
    info->fault_addr = valid ? address : 0;
    info->fault_reference_valid = valid;
}

bool snapshot_fault_reference_equal(uint64_t left_address,
                                    const ProvenanceFaultSite *left,
                                    uint64_t right_address,
                                    const ProvenanceFaultSite *right)
{
    if (left->valid != right->valid) return false;
    if (!left->valid) return left_address == right_address;
    return left->image_offset == right->image_offset &&
        memcmp(left->image_id, right->image_id, sizeof(left->image_id)) == 0;
}

void snapshot_fault_site_image_text(const ProvenanceFaultSite *site,
                                    char text[65])
{
    static const char hex[] = "0123456789abcdef";
    if (!site->valid) {
        memcpy(text, "none", 5);
        return;
    }
    for (size_t i = 0; i < sizeof(site->image_id); i++) {
        text[i * 2] = hex[site->image_id[i] >> 4];
        text[i * 2 + 1] = hex[site->image_id[i] & 15];
    }
    text[64] = '\0';
}

static int snapshot_observation_compare_primitive(const void *a, const void *b)
{
    const PrimitiveAccess *left = a;
    const PrimitiveAccess *right = b;
    if (left->access_id > right->access_id) return -1;
    if (left->access_id < right->access_id) return 1;
    return 0;
}

static int snapshot_observation_compare_pointer(const void *a, const void *b)
{
    const PointerAccess *left = a;
    const PointerAccess *right = b;
    if (left->access_id > right->access_id) return -1;
    if (left->access_id < right->access_id) return 1;
    return 0;
}

SharedTraceData *snapshot_observation_create_shared(void)
{
    SharedTraceData *shared = mmap(NULL, sizeof(*shared),
                                   PROT_READ | PROT_WRITE,
                                   MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    return shared == MAP_FAILED ? NULL : shared;
}

void snapshot_observation_destroy_shared(SharedTraceData *shared)
{
    if (shared != NULL) munmap(shared, sizeof(*shared));
}

void snapshot_observation_view_clear(SnapshotObservationView *view)
{
    if (view == NULL) return;
    g_free(view->primitives);
    g_free(view->pointers);
    memset(view, 0, sizeof(*view));
}

bool snapshot_observation_capture(const SharedTraceData *shared,
                                  SnapshotObservationView *view)
{
    bool primitive_count_valid;
    bool pointer_count_valid;

    if (shared == NULL || view == NULL) return false;
    memset(view, 0, sizeof(*view));
    view->run_epoch = shared->run_epoch;
    view->raw_primitive_count = shared->prim_idx;
    view->raw_pointer_count = shared->ptr_idx;
    view->primitive_overflow = shared->prim_overflow;
    view->pointer_overflow = shared->ptr_overflow;
    view->exit_info = shared->exit_info;

    primitive_count_valid = shared->prim_idx <= MAX_PRIMITIVE_ACCESS;
    pointer_count_valid = shared->ptr_idx <= MAX_POINTER_ACCESS;
    view->counts_valid = primitive_count_valid && pointer_count_valid &&
                         shared->prim_overflow == 0 &&
                         shared->ptr_overflow == 0;
    view->primitive_count = primitive_count_valid ? shared->prim_idx : 0;
    view->pointer_count = pointer_count_valid ? shared->ptr_idx : 0;

    if (view->primitive_count != 0) {
        view->primitives = g_try_new(PrimitiveAccess,
                                     view->primitive_count);
        if (view->primitives == NULL) goto fail;
        memcpy(view->primitives, shared->primitives,
               (size_t)view->primitive_count * sizeof(*view->primitives));
        qsort(view->primitives, view->primitive_count,
              sizeof(*view->primitives),
              snapshot_observation_compare_primitive);
    }
    if (view->pointer_count != 0) {
        view->pointers = g_try_new(PointerAccess, view->pointer_count);
        if (view->pointers == NULL) goto fail;
        memcpy(view->pointers, shared->pointers,
               (size_t)view->pointer_count * sizeof(*view->pointers));
        qsort(view->pointers, view->pointer_count,
              sizeof(*view->pointers), snapshot_observation_compare_pointer);
    }
    return true;

fail:
    snapshot_observation_view_clear(view);
    return false;
}
