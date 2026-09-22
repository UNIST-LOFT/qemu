#include "snapshot-observation.h"

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
