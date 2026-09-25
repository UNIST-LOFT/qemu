#include "snapshot-mutation-internal.h"

/*
 * Parent-owned mutation values, proposal admission, and atomic queue
 * publication.  This module owns every allocation reachable from a
 * SnapshotMutationPlan or accepted proposal family.  It deliberately knows
 * nothing about snapshot globals, OSPREY contexts, symbolic pool pointers,
 * forkserver processes, or guest application.
 */

/* Focused Stage-7 allocation-failure hook.  The production default is
 * disabled; tests set N to fail the Nth owned allocation (zero-based). */
static int64_t snapshot_mutation_alloc_fail_after = -1;

void snapshot_mutation_test_set_alloc_fail_after(int64_t fail_after)
{
    snapshot_mutation_alloc_fail_after = fail_after;
}

void *snapshot_mutation_try_malloc(size_t size)
{
    if (size == 0 || snapshot_mutation_alloc_fail_after == 0) {
        return NULL;
    }
    if (snapshot_mutation_alloc_fail_after > 0) {
        snapshot_mutation_alloc_fail_after--;
    }
    return g_try_malloc(size);
}

void *snapshot_mutation_try_malloc0(size_t size)
{
    if (size == 0 || snapshot_mutation_alloc_fail_after == 0) {
        return NULL;
    }
    if (snapshot_mutation_alloc_fail_after > 0) {
        snapshot_mutation_alloc_fail_after--;
    }
    return g_try_malloc0(size);
}

/* g_queue_pop_head() and g_queue_free_full() release links through GLib's
 * list allocator.  Links passed to g_queue_push_tail_link() must therefore
 * come from g_list_alloc(), never g_malloc(). */
static GList *snapshot_mutation_try_list_alloc(void)
{
    if (snapshot_mutation_alloc_fail_after == 0) {
        return NULL;
    }
    if (snapshot_mutation_alloc_fail_after > 0) {
        snapshot_mutation_alloc_fail_after--;
    }
    return g_list_alloc();
}

typedef struct SnapshotMutationPreparedWrite {
    SnapshotMutationWrite local;
    target_ulong before_value;
    target_ulong fresh_target;
} SnapshotMutationPreparedWrite;

SnapshotMutationApplyResult snapshot_mutation_apply(
    const SnapshotMutationPlan *plan, const SnapshotMutationApplyHost *host,
    void *opaque)
{
    SnapshotMutationPreparedWrite *writes;
    SnapshotMutationApplyResult result = SNAPSHOT_MUTATION_APPLY_OK;

    if (plan == NULL || plan->mods == NULL || plan->num_mods == 0 ||
        host == NULL || host->read_cell == NULL ||
        host->allocate_target == NULL || host->initialize_target == NULL ||
        host->publish_cell == NULL || host->observe_write == NULL) {
        return SNAPSHOT_MUTATION_APPLY_EMPTY;
    }
    writes = g_try_malloc0((size_t)plan->num_mods * sizeof(*writes));
    if (writes == NULL) {
        return SNAPSHOT_MUTATION_APPLY_ALLOCATION;
    }

    /* Validate and snapshot every destination before allocating or writing. */
    for (uint32_t i = 0; i < plan->num_mods; i++) {
        const SnapshotMutationWrite *write = &plan->mods[i];
        SnapshotMutationPreparedWrite *prepared = &writes[i];
        if (write->kind != SNAPSHOT_MUTATION_BYTES &&
            write->kind != SNAPSHOT_MUTATION_POINTER_NULL &&
            write->kind != SNAPSHOT_MUTATION_POINTER_OOB &&
            write->kind != SNAPSHOT_MUTATION_POINTER_FRESH) {
            result = SNAPSHOT_MUTATION_APPLY_KIND;
            goto out;
        }
        if (write->size == 0 || write->size > sizeof(write->value) ||
            (write->kind != SNAPSHOT_MUTATION_BYTES &&
             write->size != sizeof(target_ulong))) {
            result = SNAPSHOT_MUTATION_APPLY_WIDTH;
            goto out;
        }
        if (write->kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
            if (write->target.extent == 0 ||
                write->target.extent > SNAPSHOT_PAGE_SIZE ||
                write->target.bytes == NULL) {
                result = SNAPSHOT_MUTATION_APPLY_TARGET;
                goto out;
            }
        } else if (write->target.extent != 0 || write->target.bytes != NULL) {
            result = SNAPSHOT_MUTATION_APPLY_TARGET;
            goto out;
        }
        if (write->addr < SNAPSHOT_PAGE_SIZE) {
            if (write->addr >= CPU_NB_REGS) {
                result = SNAPSHOT_MUTATION_APPLY_REGISTER;
                goto out;
            }
            for (uint32_t prior = 0; prior < i; prior++) {
                if (writes[prior].local.addr == write->addr &&
                    writes[prior].local.addr < SNAPSHOT_PAGE_SIZE) {
                    result = SNAPSHOT_MUTATION_APPLY_DUPLICATE_REGISTER;
                    goto out;
                }
            }
        }
        for (uint32_t prior = 0; prior < i; prior++) {
            const SnapshotMutationWrite *previous = &writes[prior].local;
            uint64_t previous_end;
            uint64_t current_end;
            if (previous->addr < SNAPSHOT_PAGE_SIZE ||
                write->addr < SNAPSHOT_PAGE_SIZE) {
                continue;
            }
            previous_end = (uint64_t)previous->addr + previous->size;
            current_end = (uint64_t)write->addr + write->size;
            if ((uint64_t)write->addr < previous_end &&
                (uint64_t)previous->addr < current_end) {
                result = SNAPSHOT_MUTATION_APPLY_OVERLAP;
                goto out;
            }
        }
        prepared->local = *write;
        if (!host->read_cell(opaque, write->addr, write->size,
                             &prepared->before_value)) {
            result = SNAPSHOT_MUTATION_APPLY_DESTINATION;
            goto out;
        }
    }

    /* Initialize every fresh target before publishing any pointer cell. */
    for (uint32_t i = 0; i < plan->num_mods; i++) {
        SnapshotMutationPreparedWrite *prepared = &writes[i];
        if (prepared->local.kind != SNAPSHOT_MUTATION_POINTER_FRESH) {
            continue;
        }
        prepared->fresh_target = host->allocate_target(
            opaque, prepared->local.target.extent);
        if (prepared->fresh_target == (target_ulong)-1 ||
            !host->initialize_target(opaque, prepared->fresh_target,
                                     prepared->local.target.bytes,
                                     prepared->local.target.extent)) {
            host->observe_write(opaque, &prepared->local, 0,
                                prepared->before_value, false);
            result = SNAPSHOT_MUTATION_APPLY_FRESH_TARGET;
            goto out;
        }
        memcpy(prepared->local.value, &prepared->fresh_target,
               sizeof(prepared->fresh_target));
    }

    /* Publication cannot fail after the complete preflight above.  The guest
     * resumes only after every cell is written, so no plan can report failure
     * after exposing a multiwrite prefix. */
    for (uint32_t i = 0; i < plan->num_mods; i++) {
        SnapshotMutationPreparedWrite *prepared = &writes[i];
        host->publish_cell(opaque, &prepared->local, prepared->local.value);
        host->observe_write(opaque, &prepared->local,
                            prepared->fresh_target,
                            prepared->before_value, true);
    }

out:
    g_free(writes);
    return result;
}

void snapshot_mutation_free(SnapshotMutationPlan *mod)
{
    if (mod == NULL) {
        return;
    }
    if (mod->mods != NULL) {
        for (uint32_t i = 0; i < mod->num_mods; i++) {
            g_free(mod->mods[i].target.bytes);
        }
        g_free(mod->mods);
    }
    g_free(mod);
}

void snapshot_mutation_free_batch(SnapshotMutationPlan **mods,
                                         size_t count)
{
    if (mods == NULL) {
        return;
    }
    for (uint32_t i = 0; i < count; i++) {
        snapshot_mutation_free(mods[i]);
        mods[i] = NULL;
    }
}


SnapshotMutationPlan *snapshot_mutation_new_descriptor(
    target_ulong addr, uint32_t size, int64_t expr_index,
    int64_t query_index, SnapshotMutationKind kind, const uint8_t *value,
    uint64_t target_extent, const uint8_t *target_bytes)
{
    if (size == 0 || size > sizeof(((SnapshotMutationWrite *)0)->value)) {
        return NULL;
    }
    switch (kind) {
    case SNAPSHOT_MUTATION_BYTES:
    case SNAPSHOT_MUTATION_POINTER_NULL:
    case SNAPSHOT_MUTATION_POINTER_OOB:
    case SNAPSHOT_MUTATION_POINTER_FRESH:
        break;
    default:
        return NULL;
    }
    if (addr < SNAPSHOT_PAGE_SIZE && addr >= CPU_NB_REGS) {
        return NULL;
    }
    if (kind != SNAPSHOT_MUTATION_BYTES && size != sizeof(target_ulong)) {
        return NULL;
    }
    if (kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
        if (target_extent == 0 || target_extent > SNAPSHOT_PAGE_SIZE ||
            target_bytes == NULL || target_extent > SIZE_MAX) {
            return NULL;
        }
    } else if (target_extent != 0 || target_bytes != NULL) {
        return NULL;
    }

    SnapshotMutationPlan *plan = snapshot_mutation_try_malloc0(sizeof(*plan));
    if (plan == NULL) {
        return NULL;
    }
    plan->num_mods = 1;
    plan->mods = snapshot_mutation_try_malloc0(sizeof(*plan->mods));
    if (plan->mods == NULL) {
        snapshot_mutation_free(plan);
        return NULL;
    }

    SnapshotMutationWrite *write = &plan->mods[0];
    write->kind = kind;
    write->addr = addr;
    write->size = size;
    write->expr_index = expr_index;
    write->query_index = query_index;
    if (value != NULL) {
        memcpy(write->value, value, sizeof(write->value));
    }

    if (kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
        write->target.extent = target_extent;
        write->target.bytes = snapshot_mutation_try_malloc(
            (size_t)target_extent);
        if (write->target.bytes == NULL) {
            snapshot_mutation_free(plan);
            return NULL;
        }
        memcpy(write->target.bytes, target_bytes, (size_t)target_extent);
    }
    return plan;
}


static bool snapshot_mutation_enqueue_plan_array(
    GQueue *queue, SnapshotMutationPlan **plans, size_t count)
{
    if (queue == NULL || plans == NULL || count == 0 ||
        count > SIZE_MAX / sizeof(GList *)) {
        snapshot_mutation_free_batch(plans, count);
        return false;
    }

    GList **links = snapshot_mutation_try_malloc0(count * sizeof(*links));
    if (links == NULL) {
        snapshot_mutation_free_batch(plans, count);
        return false;
    }
    for (size_t i = 0; i < count; i++) {
        if (plans[i] == NULL) {
            for (size_t j = 0; j < i; j++) g_list_free_1(links[j]);
            g_free(links);
            snapshot_mutation_free_batch(plans, count);
            return false;
        }
        links[i] = snapshot_mutation_try_list_alloc();
        if (links[i] == NULL) {
            for (size_t j = 0; j < i; j++) g_list_free_1(links[j]);
            g_free(links);
            snapshot_mutation_free_batch(plans, count);
            return false;
        }
        links[i]->data = plans[i];
    }

    /* All links and plan ownership are complete before queue mutation. */
    for (size_t i = 0; i < count; i++) {
        g_queue_push_tail_link(queue, links[i]);
        plans[i] = NULL;
    }
    g_free(links);
    return true;
}

bool snapshot_mutation_enqueue_batch(GQueue *queue,
                                             SnapshotMutationPlan **plans,
                                             uint32_t count)
{
    return snapshot_mutation_enqueue_plan_array(queue, plans, count);
}

bool snapshot_mutation_enqueue_one(GQueue *queue,
                                           SnapshotMutationPlan *plan)
{
    SnapshotMutationPlan *batch[] = {plan};
    return snapshot_mutation_enqueue_batch(queue, batch, 1);
}


/* Per-advisor family quota.  Advisor 1 is compact OSPREY and advisor 2 is
 * symbolic boundary advice; each gets its own 4,096 slots so an advisor can
 * never consume another advisor's allocation.  The combined cap is the sum,
 * which keeps mode `off` byte-identical for OSPREY: a disabled advisor
 * reserves nothing and the OSPREY quota is unchanged. */
#define SNAPSHOT_MUTATION_MAX_SPECIALIZED_FAMILIES 4096u
#define SNAPSHOT_MUTATION_MAX_COMBINED_FAMILIES 8192u
#define SNAPSHOT_MUTATION_MAX_SPECIALIZED_VARIANTS 64u
#define SNAPSHOT_MUTATION_MAX_SPECIALIZED_WRITES 64u

/* Families already admitted for one advisor, counted over accepted copies.
 * Duplicate descriptors are not counted because they are not admitted. */
static uint32_t snapshot_mutation_advisor_family_count(
    const SnapshotMutationCoordinator *coordinator, uint32_t advisor_id)
{
    uint32_t count = 0;
    if (coordinator == NULL || coordinator->families == NULL) return 0;
    for (guint i = 0; i < coordinator->families->len; i++) {
        const SnapshotMutationProposalFamily *family =
            g_ptr_array_index(coordinator->families, i);
        if (family->advisor_id == advisor_id) count++;
    }
    return count;
}

static bool snapshot_mutation_token_equal(
    SnapshotMutationSourceToken a, SnapshotMutationSourceToken b)
{
    return a.run_epoch == b.run_epoch &&
           a.source_ordinal == b.source_ordinal;
}

const SnapshotMutationBaselineEntry *snapshot_mutation_lookup_entry(
    const SnapshotMutationBaseline *baseline,
    SnapshotMutationSourceToken token)
{
    const SnapshotMutationBaselineEntry *entry;

    if (baseline == NULL || baseline->entries == NULL ||
        token.run_epoch != baseline->run_epoch ||
        token.source_ordinal >= baseline->entry_count) {
        return NULL;
    }
    entry = &baseline->entries[token.source_ordinal];
    return snapshot_mutation_token_equal(entry->token, token) ? entry : NULL;
}

void snapshot_mutation_plan_set_source(
    SnapshotMutationPlan *plan, const SnapshotMutationBaseline *baseline,
    SnapshotMutationSourceToken primary,
    SnapshotMutationSeedSemantics seed_semantics, bool family_valid,
    uint64_t family_id)
{
    const SnapshotMutationBaselineEntry *entry;
    const SnapshotMutationWrite *primary_write = NULL;

    if (plan == NULL) return;
    plan->source_valid = false;
    plan->family_valid = false;
    plan->source_retained = false;
    plan->read_witness_applicable = false;
    plan->read_witness.valid = false;
    if (seed_semantics != SNAPSHOT_MUTATION_SEED_SNAPSHOT_STATE &&
        seed_semantics != SNAPSHOT_MUTATION_SEED_OBSERVED_READ) {
        return;
    }
    entry = snapshot_mutation_lookup_entry(baseline, primary);
    if (entry == NULL) return;

    plan->source_valid = true;
    plan->source_epoch = entry->token.run_epoch;
    plan->source_ordinal = entry->token.source_ordinal;
    plan->source_kind = entry->source_kind;
    plan->seed_semantics = seed_semantics;
    plan->family_valid = family_valid;
    plan->family_id = family_id;
    plan->source_retained = entry->observed_read_valid;

    if (entry->lane != SNAPSHOT_MUTATION_LANE_PRIMITIVE ||
        entry->source_kind != SNAPSHOT_MUTATION_SOURCE_PRIMITIVE ||
        entry->size == 0 || plan->mods == NULL || plan->num_mods == 0) {
        return;
    }
    for (uint32_t i = 0; i < plan->num_mods; i++) {
        const SnapshotMutationWrite *write = &plan->mods[i];
        if (write->addr != entry->addr) continue;
        if (primary_write != NULL || write->kind != SNAPSHOT_MUTATION_BYTES ||
            write->size != entry->size) {
            return;
        }
        primary_write = write;
    }
    if (primary_write == NULL) return;
    plan->read_witness_applicable = true;
    if (!entry->observed_read_valid ||
        entry->size > sizeof(entry->observed_read_bytes)) {
        return;
    }

    SnapshotMutationReadWitnessDescriptor *witness = &plan->read_witness;
    witness->baseline_epoch = entry->token.run_epoch;
    witness->lane = entry->lane;
    witness->access_id = entry->access_id;
    witness->pc = entry->pc;
    witness->addr = entry->addr;
    witness->width = primary_write->size;
    memcpy(witness->expected_bytes, primary_write->value,
           primary_write->size);
    witness->valid = true;
}

void snapshot_mutation_proposal_family_free(gpointer data)
{
    SnapshotMutationProposalFamily *family = data;
    if (family == NULL) return;
    if (family->variants != NULL) {
        for (uint32_t vi = 0; vi < family->variant_count; vi++) {
            SnapshotMutationProposalVariant *variant = &family->variants[vi];
            if (variant->writes != NULL) {
                for (uint32_t wi = 0; wi < variant->write_count; wi++) {
                    g_free((void *)variant->writes[wi].target_bytes);
                }
                g_free(variant->writes);
            }
        }
        g_free(family->variants);
    }
    g_free(family);
}

static bool snapshot_mutation_memory_interval(
    const SnapshotMutationBaselineEntry *entry, uint32_t size,
    uint64_t *end_out)
{
    uint64_t end;
    if (entry == NULL || size == 0 || entry->addr < SNAPSHOT_PAGE_SIZE) {
        return false;
    }
    if ((uint64_t)entry->addr > UINT64_MAX - size) return false;
    end = (uint64_t)entry->addr + size;
    if (end <= (uint64_t)entry->addr) return false;
    if (end_out != NULL) *end_out = end;
    return true;
}

bool snapshot_mutation_proposal_validate(
    const SnapshotMutationCoordinator *coordinator,
    const SnapshotMutationProposalFamily *family)
{
    const SnapshotMutationBaselineEntry *primary;
    const bool observed_read =
        family != NULL &&
        family->seed_semantics == SNAPSHOT_MUTATION_SEED_OBSERVED_READ;

    if (coordinator == NULL || coordinator->baseline == NULL ||
        family == NULL || family->advisor_id == 0 ||
        family->variants == NULL || family->variant_count == 0 ||
        family->variant_count > SNAPSHOT_MUTATION_MAX_SPECIALIZED_VARIANTS ||
        (family->seed_semantics != SNAPSHOT_MUTATION_SEED_SNAPSHOT_STATE &&
         !observed_read)) {
        return false;
    }
    primary = snapshot_mutation_lookup_entry(coordinator->baseline,
                                             family->primary_seed);
    if (primary == NULL || !primary->typed_eligible || primary->protected_addr) {
        return false;
    }
    /* An observed-read family proposes values synthesized from the bytes the
     * baseline child actually loaded.  Without a finalized observation there
     * is no source of truth to lower a candidate through, so the whole family
     * is rejected rather than silently falling back to generic semantics. */
    if (observed_read &&
        (!primary->observed_read_valid ||
         (primary->size != 1 && primary->size != 2 &&
          primary->size != 4 && primary->size != sizeof(target_ulong)) ||
         primary->lane != SNAPSHOT_MUTATION_LANE_PRIMITIVE)) {
        return false;
    }

    for (uint32_t vi = 0; vi < family->variant_count; vi++) {
        const SnapshotMutationProposalVariant *variant = &family->variants[vi];
        uint32_t primary_count = 0;
        if (variant->writes == NULL || variant->write_count == 0 ||
            variant->write_count > SNAPSHOT_MUTATION_MAX_SPECIALIZED_WRITES) {
            return false;
        }
        for (uint32_t prior_vi = 0; prior_vi < vi; prior_vi++) {
            if (family->variants[prior_vi].variant_id == variant->variant_id) {
                return false;
            }
        }
        for (uint32_t wi = 0; wi < variant->write_count; wi++) {
            const SnapshotMutationProposalWrite *write = &variant->writes[wi];
            const SnapshotMutationBaselineEntry *entry =
                snapshot_mutation_lookup_entry(coordinator->baseline,
                                               write->destination);
            uint64_t begin_a = 0, end_a = 0;
            if (entry == NULL || !entry->typed_eligible || entry->protected_addr ||
                write->size == 0 ||
                write->size > sizeof(write->value) ||
                (entry->addr >= SNAPSHOT_PAGE_SIZE &&
                 !snapshot_mutation_memory_interval(entry, write->size,
                                                    &end_a))) {
                return false;
            }
            if (observed_read && write->kind != SNAPSHOT_MUTATION_BYTES) {
                return false;
            }
            if (wi > 0 &&
                variant->writes[wi - 1].destination.source_ordinal >=
                    write->destination.source_ordinal) {
                return false;
            }
            if (snapshot_mutation_token_equal(write->destination,
                                              family->primary_seed)) {
                primary_count++;
                if (write->size != primary->size) return false;
                if (observed_read) {
                    /* Boundary advice rewrites observed scalar memory with a
                     * synthesized scalar.  A pointer-family write would
                     * replace compact OSPREY's ownership of pointer
                     * alternatives, and the value must differ from both the
                     * physical baseline bytes and the bytes the child
                     * actually read, or the child would observe no change. */
                    if (write->kind != SNAPSHOT_MUTATION_BYTES) return false;
                    if (memcmp(write->value, primary->observed_read_bytes,
                               write->size) == 0) {
                        return false;
                    }
                }
                if (write->kind != SNAPSHOT_MUTATION_POINTER_FRESH &&
                    memcmp(write->value, primary->planner_bytes,
                           write->size) == 0) {
                    return false;
                }
                if (write->kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
                    for (uint32_t bi = 0; bi < primary->size; bi++) {
                        if (primary->planner_bytes[bi] != 0) return false;
                    }
                }
            }
            switch (write->kind) {
            case SNAPSHOT_MUTATION_BYTES:
                if (write->target_extent != 0 || write->target_bytes != NULL ||
                    memcmp(write->value, entry->planner_bytes,
                           write->size) == 0) {
                    return false;
                }
                break;
            case SNAPSHOT_MUTATION_POINTER_NULL:
            case SNAPSHOT_MUTATION_POINTER_OOB:
                if (entry->size != sizeof(target_ulong) ||
                    write->size != sizeof(target_ulong) ||
                    write->target_extent != 0 || write->target_bytes != NULL ||
                    memcmp(write->value, entry->planner_bytes,
                           write->size) == 0) {
                    return false;
                }
                break;
            case SNAPSHOT_MUTATION_POINTER_FRESH:
                if (entry->size != sizeof(target_ulong) ||
                    write->size != sizeof(target_ulong) ||
                    write->target_extent == 0 ||
                    write->target_extent > SNAPSHOT_PAGE_SIZE ||
                    write->target_bytes == NULL) {
                    return false;
                }
                break;
            default:
                return false;
            }
            if (entry->addr < SNAPSHOT_PAGE_SIZE) {
                if (entry->addr >= CPU_NB_REGS) return false;
                for (uint32_t other = 0; other < wi; other++) {
                    const SnapshotMutationProposalWrite *previous =
                        &variant->writes[other];
                    const SnapshotMutationBaselineEntry *previous_entry =
                        snapshot_mutation_lookup_entry(
                            coordinator->baseline, previous->destination);
                    if (previous_entry != NULL &&
                        previous_entry->addr == entry->addr) {
                        return false;
                    }
                }
            } else {
                for (uint32_t other = 0; other < wi; other++) {
                    const SnapshotMutationProposalWrite *previous =
                        &variant->writes[other];
                    const SnapshotMutationBaselineEntry *previous_entry =
                        snapshot_mutation_lookup_entry(
                            coordinator->baseline, previous->destination);
                    uint64_t begin_b, end_b;
                    if (previous_entry == NULL ||
                        previous_entry->addr < SNAPSHOT_PAGE_SIZE ||
                        !snapshot_mutation_memory_interval(previous_entry,
                                                          previous->size,
                                                          &end_b)) {
                        continue;
                    }
                    begin_a = (uint64_t)entry->addr;
                    begin_b = (uint64_t)previous_entry->addr;
                    if (begin_a < end_b && begin_b < end_a) return false;
                }
            }
        }
        if (primary_count != 1) return false;
    }
    return true;
}

static SnapshotMutationProposalFamily *snapshot_mutation_proposal_copy(
    const SnapshotMutationProposalFamily *source)
{
    SnapshotMutationProposalFamily *copy;

    if (source == NULL) return NULL;
    copy = snapshot_mutation_try_malloc0(sizeof(*copy));
    if (copy == NULL) return NULL;
    *copy = *source;
    copy->variants = snapshot_mutation_try_malloc0(
        (size_t)source->variant_count * sizeof(*copy->variants));
    if (copy->variants == NULL) {
        snapshot_mutation_proposal_family_free(copy);
        return NULL;
    }
    for (uint32_t vi = 0; vi < source->variant_count; vi++) {
        const SnapshotMutationProposalVariant *src = &source->variants[vi];
        SnapshotMutationProposalVariant *dst = &copy->variants[vi];
        *dst = *src;
        dst->writes = snapshot_mutation_try_malloc0(
            (size_t)src->write_count * sizeof(*dst->writes));
        if (dst->writes == NULL) {
            snapshot_mutation_proposal_family_free(copy);
            return NULL;
        }
        for (uint32_t wi = 0; wi < src->write_count; wi++) {
            const SnapshotMutationProposalWrite *src_write = &src->writes[wi];
            SnapshotMutationProposalWrite *dst_write = &dst->writes[wi];
            *dst_write = *src_write;
            dst_write->target_bytes = NULL;
            if (src_write->kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
                if (src_write->target_bytes == NULL ||
                    src_write->target_extent == 0 ||
                    src_write->target_extent > SIZE_MAX) {
                    snapshot_mutation_proposal_family_free(copy);
                    return NULL;
                }
                uint8_t *payload = snapshot_mutation_try_malloc(
                    (size_t)src_write->target_extent);
                if (payload == NULL) {
                    snapshot_mutation_proposal_family_free(copy);
                    return NULL;
                }
                memcpy(payload, src_write->target_bytes,
                       (size_t)src_write->target_extent);
                dst_write->target_bytes = payload;
            }
        }
    }
    return copy;
}

static bool snapshot_mutation_proposal_same_descriptor(
    const SnapshotMutationProposalFamily *a,
    const SnapshotMutationProposalFamily *b)
{
    if (a == NULL || b == NULL || a->advisor_id != b->advisor_id ||
        a->family_id != b->family_id ||
        !snapshot_mutation_token_equal(a->primary_seed, b->primary_seed) ||
        a->seed_semantics != b->seed_semantics ||
        a->variant_count != b->variant_count) {
        return false;
    }
    for (uint32_t vi = 0; vi < a->variant_count; vi++) {
        const SnapshotMutationProposalVariant *av = &a->variants[vi];
        const SnapshotMutationProposalVariant *bv = &b->variants[vi];
        if (av->variant_id != bv->variant_id ||
            av->write_count != bv->write_count) return false;
        for (uint32_t wi = 0; wi < av->write_count; wi++) {
            const SnapshotMutationProposalWrite *aw = &av->writes[wi];
            const SnapshotMutationProposalWrite *bw = &bv->writes[wi];
            if (!snapshot_mutation_token_equal(aw->destination,
                                               bw->destination) ||
                aw->kind != bw->kind || aw->size != bw->size ||
                memcmp(aw->value, bw->value, sizeof(aw->value)) != 0 ||
                aw->target_extent != bw->target_extent ||
                aw->resolved_raw != bw->resolved_raw ||
                aw->resolved_end != bw->resolved_end) return false;
            if (aw->target_extent != 0 &&
                (aw->target_bytes == NULL || bw->target_bytes == NULL ||
                 memcmp(aw->target_bytes, bw->target_bytes,
                        (size_t)aw->target_extent) != 0)) return false;
        }
    }
    return true;
}

bool snapshot_mutation_sink_submit(
    SnapshotMutationProposalSink *sink,
    const SnapshotMutationProposalFamily *family)
{
    SnapshotMutationProposalFamily *copy;
    if (sink == NULL || sink->coordinator == NULL || family == NULL ||
        family->advisor_id != sink->advisor_id ||
        family->advisor_priority != sink->advisor_priority ||
        sink->coordinator->families == NULL ||
        sink->coordinator->families->len >=
            SNAPSHOT_MUTATION_MAX_COMBINED_FAMILIES ||
        snapshot_mutation_advisor_family_count(sink->coordinator,
                                               sink->advisor_id) >=
            SNAPSHOT_MUTATION_MAX_SPECIALIZED_FAMILIES ||
        !snapshot_mutation_proposal_validate(sink->coordinator, family)) {
        return false;
    }
    for (guint i = 0; i < sink->coordinator->families->len; i++) {
        SnapshotMutationProposalFamily *existing =
            g_ptr_array_index(sink->coordinator->families, i);
        if (snapshot_mutation_proposal_same_descriptor(existing, family)) {
            return true;
        }
    }
    copy = snapshot_mutation_proposal_copy(family);
    if (copy == NULL) return false;
    g_ptr_array_add(sink->coordinator->families, copy);
    return true;
}

void snapshot_mutation_baseline_free(
    SnapshotMutationBaseline *baseline)
{
    if (baseline == NULL) return;
    g_free(baseline->entries);
    g_free(baseline);
}

void snapshot_mutation_coordinator_clear(
    SnapshotMutationCoordinator *coordinator)
{
    if (coordinator == NULL) return;
    if (coordinator->families != NULL) {
        g_ptr_array_free(coordinator->families, TRUE);
        coordinator->families = NULL;
    }
    if (coordinator->staged != NULL) {
        g_ptr_array_free(coordinator->staged, TRUE);
        coordinator->staged = NULL;
    }
    coordinator->baseline = NULL;
}


static gint snapshot_mutation_family_compare(gconstpointer left,
                                             gconstpointer right,
                                             gpointer user_data)
{
    const SnapshotMutationProposalFamily *a =
        *(const SnapshotMutationProposalFamily * const *)left;
    const SnapshotMutationProposalFamily *b =
        *(const SnapshotMutationProposalFamily * const *)right;
    const SnapshotMutationBaseline *baseline = user_data;
    const SnapshotMutationBaselineEntry *ae =
        snapshot_mutation_lookup_entry(baseline, a->primary_seed);
    const SnapshotMutationBaselineEntry *be =
        snapshot_mutation_lookup_entry(baseline, b->primary_seed);
    if (ae != NULL && be != NULL && ae->token.source_ordinal !=
                                      be->token.source_ordinal) {
        return ae->token.source_ordinal < be->token.source_ordinal ? -1 : 1;
    }
    if (a->advisor_priority != b->advisor_priority)
        return a->advisor_priority < b->advisor_priority ? -1 : 1;
    if (a->family_id != b->family_id)
        return a->family_id < b->family_id ? -1 : 1;
    if (a->advisor_id != b->advisor_id)
        return a->advisor_id < b->advisor_id ? -1 : 1;
    return 0;
}


void snapshot_mutation_coordinator_sort(SnapshotMutationCoordinator *coordinator)
{
    if (coordinator == NULL || coordinator->families == NULL) {
        return;
    }
    g_ptr_array_sort_with_data(coordinator->families,
                               snapshot_mutation_family_compare,
                               (gpointer)coordinator->baseline);
}

bool snapshot_mutation_coordinator_init(
    SnapshotMutationCoordinator *coordinator,
    const SnapshotMutationBaseline *baseline)
{
    if (coordinator == NULL || baseline == NULL) {
        return false;
    }
    memset(coordinator, 0, sizeof(*coordinator));
    coordinator->baseline = baseline;
    coordinator->families = g_ptr_array_new_with_free_func(
        snapshot_mutation_proposal_family_free);
    coordinator->staged = g_ptr_array_new_with_free_func(
        (GDestroyNotify)snapshot_mutation_free);
    if (coordinator->families == NULL || coordinator->staged == NULL) {
        snapshot_mutation_coordinator_clear(coordinator);
        return false;
    }
    return true;
}

/* Build one owned plan for one complete proposal variant.  Every write in a
 * variant is applied by a single disposable child, so the plan must carry the
 * whole write set atomically: num_mods equals write_count and no partial plan
 * is ever published.  Fresh payloads are deep-copied into plan ownership so
 * the child never reads proponent-owned bytes. */
static SnapshotMutationPlan *snapshot_mutation_new_variant(
    const SnapshotMutationBaseline *baseline,
    const SnapshotMutationProposalVariant *variant)
{
    SnapshotMutationPlan *plan;

    if (baseline == NULL || variant == NULL || variant->writes == NULL ||
        variant->write_count == 0 ||
        variant->write_count > SNAPSHOT_MUTATION_MAX_SPECIALIZED_WRITES) {
        return NULL;
    }
    plan = snapshot_mutation_try_malloc0(sizeof(*plan));
    if (plan == NULL) return NULL;
    plan->num_mods = variant->write_count;
    plan->mods = snapshot_mutation_try_malloc0(
        (size_t)variant->write_count * sizeof(*plan->mods));
    if (plan->mods == NULL) {
        snapshot_mutation_free(plan);
        return NULL;
    }

    for (uint32_t wi = 0; wi < variant->write_count; wi++) {
        const SnapshotMutationProposalWrite *write = &variant->writes[wi];
        const SnapshotMutationBaselineEntry *entry =
            snapshot_mutation_lookup_entry(baseline, write->destination);
        SnapshotMutationWrite *mod = &plan->mods[wi];

        if (entry == NULL || write->size == 0 ||
            write->size > sizeof(mod->value)) {
            snapshot_mutation_free(plan);
            return NULL;
        }
        if (write->kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
            if (write->target_extent == 0 ||
                write->target_extent > SNAPSHOT_PAGE_SIZE ||
                write->target_bytes == NULL ||
                write->target_extent > SIZE_MAX) {
                snapshot_mutation_free(plan);
                return NULL;
            }
            mod->target.bytes = snapshot_mutation_try_malloc(
                (size_t)write->target_extent);
            if (mod->target.bytes == NULL) {
                snapshot_mutation_free(plan);
                return NULL;
            }
            memcpy(mod->target.bytes, write->target_bytes,
                   (size_t)write->target_extent);
        } else if (write->kind != SNAPSHOT_MUTATION_BYTES &&
                   write->kind != SNAPSHOT_MUTATION_POINTER_NULL &&
                   write->kind != SNAPSHOT_MUTATION_POINTER_OOB) {
            snapshot_mutation_free(plan);
            return NULL;
        }
        mod->kind = write->kind;
        mod->addr = entry->addr;
        mod->size = write->size;
        mod->expr_index = entry->expr_index;
        mod->query_index = entry->query_index;
        memcpy(mod->value, write->value, sizeof(mod->value));
        mod->target.extent = write->target_extent;
        mod->target.resolved_raw = write->resolved_raw;
        mod->target.resolved_end = write->resolved_end;
    }
    return plan;
}

bool snapshot_mutation_stage_family(
    SnapshotMutationCoordinator *coordinator,
    const SnapshotMutationProposalFamily *family)
{
    GPtrArray *local;
    if (coordinator == NULL || family == NULL) return false;
    local = g_ptr_array_new_with_free_func(
        (GDestroyNotify)snapshot_mutation_free);
    if (local == NULL) return false;
    for (uint32_t vi = 0; vi < family->variant_count; vi++) {
        SnapshotMutationPlan *plan = snapshot_mutation_new_variant(
            coordinator->baseline, &family->variants[vi]);
        if (plan == NULL) {
            g_ptr_array_free(local, TRUE);
            return false;
        }
        plan->advisor_id = family->advisor_id;
        snapshot_mutation_plan_set_source(
            plan, coordinator->baseline, family->primary_seed,
            family->seed_semantics, true, family->family_id);
        g_ptr_array_add(local, plan);
    }
    for (guint i = 0; i < local->len; i++) {
        SnapshotMutationPlan *plan = g_ptr_array_index(local, i);
        g_ptr_array_index(local, i) = NULL;
        g_ptr_array_add(coordinator->staged, plan);
    }
    g_ptr_array_set_size(local, 0);
    g_ptr_array_free(local, TRUE);
    return true;
}


bool snapshot_mutation_coordinator_publish(
    SnapshotMutationCoordinator *coordinator, GQueue *queue)
{
    if (coordinator == NULL || coordinator->baseline == NULL ||
        coordinator->staged == NULL || queue == NULL) return false;
    if (coordinator->staged->len == 0) return true;
    SnapshotMutationPlan **plans = (SnapshotMutationPlan **)
        coordinator->staged->pdata;
    size_t count = coordinator->staged->len;
    bool ok = snapshot_mutation_enqueue_plan_array(queue, plans, count);
    g_ptr_array_set_size(coordinator->staged, 0);
    return ok;
}

