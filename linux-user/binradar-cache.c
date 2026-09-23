#include "binradar-cache.h"
#include "snapshot-observation.h"

#include <fcntl.h>
#include <unistd.h>
#include "qapi/error.h"
#include "qapi/qmp/qdict.h"
#include "qapi/qmp/qjson.h"
#include "qapi/qmp/qlist.h"
#include "qapi/qmp/qnum.h"

static int binradar_cache_write_exact(int fd, const void *buf, size_t len)
{
    const uint8_t *p = buf;
    size_t total = 0;
    while (total < len) {
        ssize_t n = write(fd, p + total, len - total);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) return -1;
        total += (size_t)n;
    }
    return 0;
}

BinradarResult *binradar_cache_new_iteration(BinradarManager *manager) {
    if (manager == NULL) return NULL;
    BinradarResult *result = g_new0(BinradarResult, 1);
    result->iter = 0;
    result->patch_results = g_new0(PatchedResult, manager->patch_max_id + 1);
    return result;
}


int binradar_cache_patch_id(BinradarManager *manager, int new_patch_id) {
    if (manager == NULL) return -1;
    if (manager->current == NULL) return -1;
    if (new_patch_id >= 0) {
        *manager->cur_patch_id = new_patch_id;
    }
    return *manager->cur_patch_id;
}

int binradar_cache_iteration(BinradarManager *manager, int new_iter) {
    if (manager == NULL) return -1;
    if (manager->current == NULL) return -1;
    if (new_iter >= 0) {
        *manager->cur_iter = new_iter;
    }
    return *manager->cur_iter;
}

// Actual patch id for iteration index (0 = original program, then candidates)
int binradar_cache_patch_id_at(const BinradarManager *manager, uint32_t index) {
    if (manager == NULL) return 0;
    if (index == 0) return 0;
    if (index > manager->patch_cnt) return 0;
    if (manager->patch_list == NULL) return (int)index;
    return (int)manager->patch_list[index - 1];
}


uint16_t br_evidence_read_u16(const uint8_t *p)
{
    return (uint16_t)p[0] | ((uint16_t)p[1] << 8);
}

uint32_t br_evidence_read_u32(const uint8_t *p)
{
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) |
           ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

static void br_evidence_append_u16(GByteArray *out, uint16_t value)
{
    uint8_t bytes[2] = {(uint8_t)value, (uint8_t)(value >> 8)};
    g_byte_array_append(out, bytes, sizeof(bytes));
}

static void br_evidence_append_u32(GByteArray *out, uint32_t value)
{
    uint8_t bytes[4] = {
        (uint8_t)value, (uint8_t)(value >> 8),
        (uint8_t)(value >> 16), (uint8_t)(value >> 24),
    };
    g_byte_array_append(out, bytes, sizeof(bytes));
}

static void br_evidence_append_u64(GByteArray *out, uint64_t value)
{
    uint8_t bytes[8];
    for (unsigned i = 0; i < sizeof(bytes); i++) {
        bytes[i] = (uint8_t)(value >> (i * 8u));
    }
    g_byte_array_append(out, bytes, sizeof(bytes));
}

static void br_evidence_append_uleb32(GByteArray *out, uint32_t value)
{
    do {
        uint8_t byte = (uint8_t)(value & 0x7fu);
        value >>= 7;
        if (value != 0) byte |= 0x80u;
        g_byte_array_append(out, &byte, 1);
    } while (value != 0);
}

static uint32_t br_evidence_crc32_update(uint32_t crc,
                                         const uint8_t *data, size_t len)
{
    crc = ~crc;
    for (size_t i = 0; i < len; i++) {
        crc ^= data[i];
        for (unsigned bit = 0; bit < 8; bit++) {
            uint32_t mask = (uint32_t)-(int32_t)(crc & 1u);
            crc = (crc >> 1) ^ (0xedb88320u & mask);
        }
    }
    return ~crc;
}

uint32_t br_evidence_frame_crc(uint16_t type, uint16_t flags,
                                      const uint8_t *payload, size_t len)
{
    uint8_t prefix[4] = {
        (uint8_t)type, (uint8_t)(type >> 8),
        (uint8_t)flags, (uint8_t)(flags >> 8),
    };
    uint32_t crc = br_evidence_crc32_update(0, prefix, sizeof(prefix));
    return br_evidence_crc32_update(crc, payload, len);
}

bool br_evidence_write_header(FILE *fp, uint16_t kind)
{
    GByteArray *header = g_byte_array_sized_new(BR_EVIDENCE_HEADER_SIZE);
    g_byte_array_append(header, (const uint8_t *)BR_EVIDENCE_MAGIC, 8);
    br_evidence_append_u16(header, kind == BR_EVIDENCE_KIND_BINRADAR
        ? BR_EVIDENCE_VERSION_BINRADAR : BR_EVIDENCE_VERSION);
    br_evidence_append_u16(header, kind);
    br_evidence_append_u32(header, 0);
    bool ok = fwrite(header->data, 1, header->len, fp) == header->len;
    g_byte_array_free(header, TRUE);
    return ok;
}

static bool br_evidence_write_frame(FILE *fp, uint16_t type,
                                    const GByteArray *payload)
{
    if (payload->len > BR_EVIDENCE_MAX_FRAME) return false;
    GByteArray *header = g_byte_array_sized_new(
        BR_EVIDENCE_FRAME_HEADER_SIZE);
    br_evidence_append_u32(header, payload->len);
    br_evidence_append_u16(header, type);
    br_evidence_append_u16(header, 0);
    uint32_t crc = br_evidence_frame_crc(type, 0, payload->data, payload->len);
    uint8_t checksum[4] = {
        (uint8_t)crc, (uint8_t)(crc >> 8),
        (uint8_t)(crc >> 16), (uint8_t)(crc >> 24),
    };
    bool ok = fwrite(header->data, 1, header->len, fp) == header->len &&
              fwrite(payload->data, 1, payload->len, fp) == payload->len &&
              fwrite(checksum, 1, sizeof(checksum), fp) == sizeof(checksum) &&
              fflush(fp) == 0;
    g_byte_array_free(header, TRUE);
    return ok;
}


static const char *binradar_feedback_mutation_kind(SnapshotMutationKind kind)
{
    switch (kind) {
    case SNAPSHOT_MUTATION_BYTES: return "bytes";
    case SNAPSHOT_MUTATION_POINTER_NULL: return "pointer-null";
    case SNAPSHOT_MUTATION_POINTER_OOB: return "pointer-oob";
    case SNAPSHOT_MUTATION_POINTER_FRESH: return "pointer-fresh";
    }
    return "invalid";
}

static bool binradar_cache_feedback_write_atomic(const char *path,
                                           const void *data, size_t size)
{
    bool ok = false;
    char *temporary = g_strdup_printf("%s.tmp-%ld", path, (long)getpid());
    int fd = open(temporary, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (fd >= 0) {
        bool complete = binradar_cache_write_exact(fd, data, size) == 0 && fsync(fd) == 0;
        int close_status = close(fd);
        fd = -1;
        if (complete && close_status == 0 && rename(temporary, path) == 0) {
            ok = true;
        }
    }
    if (!ok) unlink(temporary);
    g_free(temporary);
    return ok;
}

/* Stage one pair for one real child execution.  Cache-materialized members
 * never call this function: they have no child-local snapshot of their own.
 *
 * The pair is written under the attempt's staging directory and is renamed
 * into ``feedback_dir`` only by binradar_cache_feedback_publish().  A
 * discarded attempt drops it, so committed sweep evidence never carries a
 * pair produced by an attempt that never committed. */
bool binradar_cache_feedback_write(
    BinradarManager *manager, uint32_t iteration, uint32_t patch_id,
    const GArray *branches, const BinradarMutationFeedbackView *mutation)
{
    if (manager == NULL || manager->feedback_dir == NULL || iteration <= 1 ||
        manager->cache_bytes == NULL || branches == NULL) return true;
    PatchedResult *run = binradar_cache_result(manager, patch_id);
    if (run->patch_id != patch_id || run->representative != patch_id) {
        return false;
    }
    if (manager->feedback_staging_dir == NULL) {
        manager->feedback_staging_dir = g_strdup_printf(
            "%s/.staging-%ld", manager->feedback_dir, (long)getpid());
        if (g_mkdir_with_parents(manager->feedback_staging_dir, 0700) != 0) {
            g_free(manager->feedback_staging_dir);
            manager->feedback_staging_dir = NULL;
            log_msg("[binradar] [feedback] [error staging] "
                    "[iter %u] [patch %u]\n", iteration, patch_id);
            return false;
        }
    }
    if (manager->feedback_staged_pairs == NULL) {
        manager->feedback_staged_pairs = g_ptr_array_new_with_free_func(
            g_free);
    }

    char *stem = g_strdup_printf("iteration-%08u-patch-%08u",
                                 iteration, patch_id);
    char *snapshot_name = g_strconcat(stem, ".brch", NULL);
    char *metadata_name = g_strconcat(stem, ".sbsv", NULL);
    char *snapshot_path = g_build_filename(manager->feedback_staging_dir,
                                           snapshot_name, NULL);
    char *metadata_path = g_build_filename(manager->feedback_staging_dir,
                                           metadata_name, NULL);
    GString *metadata = g_string_new(NULL);
    const bool same_fault = run->is_crash &&
        run->fault_reference_valid && manager->poc_fault_valid &&
        run->fault_loc == manager->poc_fault_addr;
    const char *result = !run->is_crash ? "benign" :
        same_fault ? "malicious" : "ignored";
    const uint32_t mutation_writes = mutation != NULL
        ? mutation->write_count : 0;

    GString *branch_text = g_string_new(NULL);
    if (branches->len == 0) {
        g_string_append(branch_text, "none");
    } else {
        for (guint i = 0; i < branches->len; i++) {
            if (i != 0) g_string_append_c(branch_text, ',');
            g_string_append_printf(branch_text, "%d",
                g_array_index(branches, int, i));
        }
    }
    g_string_append_printf(metadata,
        "[binradar-feedback] [version 2] [iteration %u] [patch %u] "
        "[snapshot-file %s] [snapshot-count %u] [branches %s] "
        "[outcome %s] [fault-addr %lx] [fault-valid %s] "
        "[fault-source %s] [poc-fault-addr %lx] [poc-fault-valid %s] "
        "[poc-fault-source %s] [same-fault %s] [result %s] "
        "[mutation-writes %u]\n",
        iteration, patch_id, snapshot_name, branches->len, branch_text->str,
        run->is_crash ? "crash" : "normal", run->fault_loc,
        run->fault_reference_valid ? "true" : "false",
        snapshot_fault_reference_source_name(run->fault_reference_source),
        manager->poc_fault_addr, manager->poc_fault_valid ? "true" : "false",
        snapshot_fault_reference_source_name(manager->poc_fault_source),
        same_fault ? "true" : "false", result, mutation_writes);
    g_string_free(branch_text, TRUE);

    for (uint32_t i = 0; mutation != NULL &&
                         i < mutation->write_count; i++) {
        const SnapshotMutationWrite *write = &mutation->writes[i];
        g_string_append_printf(metadata,
            "[binradar-mutation] [index %u] [kind %s] "
            "[addr %lx] [size %u] [value ", i,
            binradar_feedback_mutation_kind(write->kind), write->addr,
            write->size);
        if (write->kind == SNAPSHOT_MUTATION_POINTER_FRESH) {
            g_string_append(metadata, "dynamic");
        } else {
            for (uint32_t byte = 0; byte < write->size; byte++) {
                g_string_append_printf(metadata, "%02x", write->value[byte]);
            }
        }
        g_string_append_printf(metadata, "] [target-extent %llu]\n",
            (unsigned long long)write->target.extent);
    }

    bool ok = binradar_cache_feedback_write_atomic(
        snapshot_path, manager->cache_bytes->data, manager->cache_bytes->len);
    if (ok) {
        ok = binradar_cache_feedback_write_atomic(metadata_path, metadata->str,
                                            metadata->len);
    }
    if (!ok) {
        unlink(snapshot_path);
        unlink(metadata_path);
        log_msg("[binradar] [feedback] [error write] [iter %u] [patch %u]\n",
                iteration, patch_id);
    } else {
        g_ptr_array_add(manager->feedback_staged_pairs,
                        g_strdup(snapshot_name));
        g_ptr_array_add(manager->feedback_staged_pairs,
                        g_strdup(metadata_name));
        log_msg("[binradar] [feedback] [staged] [iter %u] [patch %u] "
                "[snapshots %u] [bytes %u] [result %s]\n",
                iteration, patch_id, branches->len, manager->cache_bytes->len,
                result);
    }
    g_string_free(metadata, TRUE);
    g_free(metadata_path);
    g_free(snapshot_path);
    g_free(metadata_name);
    g_free(snapshot_name);
    g_free(stem);
    return ok;
}

/* Rename every staged pair into the feedback directory.  Called only after
 * the attempt's evidence frame is committed.  Publication is all-or-none for
 * the run: a collision or rename failure rolls back files already moved and
 * makes the caller fail the phase instead of leaving a partial pair. */
bool binradar_cache_feedback_publish(BinradarManager *manager)
{
    GPtrArray *published;
    bool ok = true;

    if (manager == NULL) return false;
    if (manager->feedback_staging_dir == NULL) return true;
    if (manager->feedback_staged_pairs == NULL) {
        binradar_cache_feedback_drop(manager);
        return true;
    }
    published = g_ptr_array_new_with_free_func(g_free);
    for (guint i = 0; i < manager->feedback_staged_pairs->len; i++) {
        const char *name = g_ptr_array_index(manager->feedback_staged_pairs, i);
        char *source = g_build_filename(manager->feedback_staging_dir,
                                        name, NULL);
        char *destination = g_build_filename(manager->feedback_dir, name,
                                             NULL);
        if (g_file_test(destination, G_FILE_TEST_EXISTS) ||
            rename(source, destination) != 0) {
            log_msg("[binradar] [feedback] [error publish] [file %s]\n", name);
            ok = false;
        } else {
            g_ptr_array_add(published, destination);
            destination = NULL;
        }
        g_free(destination);
        g_free(source);
        if (!ok) break;
    }
    if (!ok) {
        for (guint i = 0; i < published->len; i++) {
            unlink(g_ptr_array_index(published, i));
        }
    }
    g_ptr_array_free(published, TRUE);
    binradar_cache_feedback_drop(manager);
    return ok;
}

/* Drop every staged pair of the current attempt without publishing it. */
void binradar_cache_feedback_drop(BinradarManager *manager)
{
    if (manager == NULL) return;
    if (manager->feedback_staging_dir != NULL &&
        manager->feedback_staged_pairs != NULL) {
        for (guint i = 0; i < manager->feedback_staged_pairs->len; i++) {
            const char *name =
                g_ptr_array_index(manager->feedback_staged_pairs, i);
            char *path = g_build_filename(manager->feedback_staging_dir,
                                          name, NULL);
            unlink(path);
            g_free(path);
        }
    }
    if (manager->feedback_staged_pairs != NULL) {
        g_ptr_array_set_size(manager->feedback_staged_pairs, 0);
    }
    if (manager->feedback_staging_dir != NULL) {
        rmdir(manager->feedback_staging_dir);
        g_free(manager->feedback_staging_dir);
        manager->feedback_staging_dir = NULL;
    }
}

/* Release feedback staging ownership when the manager is torn down. */
void binradar_cache_feedback_release(BinradarManager *manager)
{
    if (manager == NULL) return;
    binradar_cache_feedback_drop(manager);
    if (manager->feedback_staged_pairs != NULL) {
        g_ptr_array_free(manager->feedback_staged_pairs, TRUE);
        manager->feedback_staged_pairs = NULL;
    }
}

void binradar_cache_disable(BinradarManager *manager,
                                   const char *reason)
{
    if (!manager->cache_inference_enabled) return;
    manager->cache_inference_enabled = false;
    log_msg("[binradar] [cache-disabled] [reason %s]\n", reason);
}

bool binradar_cache_publish_selector(BinradarManager *manager,
                                      uint32_t patch_id, uint32_t iteration)
{
    if (!manager->cache_enabled) {
        binradar_cache_patch_id(manager, (int)patch_id);
        binradar_cache_iteration(manager, (int)iteration);
        return true;
    }
    const char *descriptor = patch_id == 0 ? "p0" :
        manager->cache_predicates[patch_id].descriptor;
    size_t length = descriptor != NULL ? strlen(descriptor) : 0;
    if (length >= manager->selector->descriptor_capacity) return false;

    /* Iteration is the publication flag.  Keep it at the unpublished value
     * until the complete descriptor and patch id are visible. */
    binradar_cache_iteration(manager, 0);
    __sync_synchronize();
    memcpy(manager->selector->descriptor, descriptor, length + 1u);
    manager->selector->descriptor_length = (uint32_t)length;
    binradar_cache_patch_id(manager, (int)patch_id);
    __sync_synchronize();
    binradar_cache_iteration(manager, (int)iteration);
    return true;
}

void binradar_cache_clear_iteration(BinradarManager *manager)
{
    if (manager == NULL || manager->current == NULL) return;
    for (uint32_t patch = 0; patch <= manager->patch_max_id; patch++) {
        PatchedResult *result = &manager->current->patch_results[patch];
        if (result->br_taken != NULL) {
            g_array_free(result->br_taken, TRUE);
        }
    }
    memset(manager->current->patch_results, 0,
           sizeof(PatchedResult) * (manager->patch_max_id + 1u));
}

void binradar_cache_restore_uncovered(BinradarManager *manager,
                                                  bool *uncovered,
                                                  const bool *executed)
{
    if (manager == NULL || uncovered == NULL || executed == NULL) return;
    for (uint32_t i = 0; i < manager->patch_cnt; i++) {
        uint32_t patch = (uint32_t)binradar_cache_patch_id_at(manager,
                                                                i + 1u);
        if (executed[patch]) continue;
        PatchedResult *result = binradar_cache_result(manager, patch);
        if (result->br_taken != NULL) {
            g_array_free(result->br_taken, TRUE);
        }
        memset(result, 0, sizeof(*result));
        uncovered[patch] = true;
    }
}

static GArray *binradar_clone_branch_vector(const GArray *source)
{
    GArray *clone = g_array_sized_new(FALSE, FALSE, sizeof(int), source->len);
    if (source->len != 0) {
        g_array_append_vals(clone, source->data, source->len);
    }
    return clone;
}

void binradar_cache_record_outcome(BinradarManager *manager,
                                    uint32_t patch_id,
                                    const SnapshotExitInfo *info)
{
    PatchedResult *result = binradar_cache_result(manager, patch_id);
    if (info == NULL || !info->valid) return;
    result->patch_id = patch_id;
    result->representative = patch_id;
    result->is_crash = info->crashed;
    result->fault_reference_valid = info->fault_reference_valid != 0;
    result->fault_reference_source = info->fault_reference_source;
    result->fault_loc = info->fault_addr;
}

void binradar_cache_materialize(BinradarManager *manager,
                                 uint32_t patch_id,
                                 uint32_t representative,
                                 const GArray *branches,
                                 const SnapshotExitInfo *info)
{
    PatchedResult *result = binradar_cache_result(manager, patch_id);
    result->patch_id = patch_id;
    result->representative = representative;
    result->br_taken = branches->len == 0
        ? NULL : binradar_clone_branch_vector(branches);
    if (info != NULL && info->valid) {
        result->is_crash = info->crashed;
        result->fault_reference_valid = info->fault_reference_valid != 0;
        result->fault_reference_source = info->fault_reference_source;
        result->fault_loc = info->fault_addr;
    }
}

static gint binradar_compare_u32(gconstpointer left, gconstpointer right)
{
    uint32_t a = *(const uint32_t *)left;
    uint32_t b = *(const uint32_t *)right;
    return a < b ? -1 : a > b;
}

bool binradar_cache_commit(BinradarManager *manager)
{
    GArray **members = NULL;
    GByteArray *payload = NULL;
    bool ok = false;
    uint32_t group_count = 0;

    if (manager == NULL || manager->current == NULL ||
        manager->evidence_file == NULL) return true;
    int cur_iter = binradar_cache_iteration(manager, -1);
    if (cur_iter < 1) return true;
    uint32_t result_count = cur_iter == 1 ? 1u : manager->patch_cnt + 1u;

    members = g_try_new0(GArray *, manager->patch_max_id + 1u);
    if (members == NULL) return false;
    for (uint32_t i = 0; i < result_count; i++) {
        uint32_t patch = (uint32_t)binradar_cache_patch_id_at(manager, i);
        PatchedResult *result = &manager->current->patch_results[patch];
        uint32_t representative = result->representative;
        if (result->patch_id != patch ||
            representative > manager->patch_max_id ||
            (result->is_crash &&
             (!result->fault_reference_valid ||
              (result->fault_reference_source !=
                   SNAPSHOT_FAULT_REFERENCE_GUEST_SIGNAL &&
               result->fault_reference_source !=
                   SNAPSHOT_FAULT_REFERENCE_PROVENANCE_ACCESS)))) {
            log_msg("[binradar] [evidence] [error incomplete-result] "
                    "[iter %d] [patch %u]\n", cur_iter, patch);
            goto out;
        }
        if (members[representative] == NULL) {
            members[representative] = g_array_new(FALSE, FALSE,
                                                   sizeof(uint32_t));
            group_count++;
        }
        g_array_append_val(members[representative], patch);
    }

    payload = g_byte_array_new();
    br_evidence_append_u32(payload, (uint32_t)cur_iter);
    br_evidence_append_u32(payload, group_count);
    for (uint32_t i = 0; i < result_count; i++) {
        uint32_t representative =
            (uint32_t)binradar_cache_patch_id_at(manager, i);
        GArray *group = members[representative];
        if (group == NULL) continue;
        g_array_sort(group, binradar_compare_u32);
        PatchedResult *result =
            &manager->current->patch_results[representative];
        uint8_t outcome = result->is_crash
            ? BR_EVIDENCE_OUTCOME_CRASH : BR_EVIDENCE_OUTCOME_NORMAL;
        uint8_t flags = result->br_taken == NULL
            ? BR_EVIDENCE_GROUP_BRANCH_NULL : 0;
        uint32_t branch_count = result->br_taken != NULL
            ? result->br_taken->len : 0;

        br_evidence_append_u32(payload, representative);
        g_byte_array_append(payload, &outcome, 1);
        g_byte_array_append(payload, &flags, 1);
        br_evidence_append_u16(payload, 0);
        br_evidence_append_u64(payload, result->fault_loc);
        br_evidence_append_u32(payload, branch_count);
        br_evidence_append_u32(payload, group->len);

        uint8_t packed = 0;
        for (uint32_t branch = 0; branch < branch_count; branch++) {
            int value = g_array_index(result->br_taken, int, branch);
            if (value < 0 || value > 2) {
                log_msg("[binradar] [evidence] [error branch] "
                        "[iter %d] [patch %u]\n", cur_iter,
                        representative);
                goto out;
            }
            packed |= (uint8_t)value << ((branch % 4u) * 2u);
            if (branch % 4u == 3u || branch + 1u == branch_count) {
                g_byte_array_append(payload, &packed, 1);
                packed = 0;
            }
        }

        uint32_t previous = 0;
        for (guint member_index = 0; member_index < group->len;
             member_index++) {
            uint32_t member = g_array_index(group, uint32_t, member_index);
            uint32_t delta = member_index == 0 ? member : member - previous;
            br_evidence_append_uleb32(payload, delta);
            previous = member;
        }
    }

    if (!br_evidence_write_frame(manager->evidence_file,
                                  BR_EVIDENCE_RECORD_BINRADAR_ITERATION,
                                  payload)) {
        log_msg("[binradar] [evidence] [error write] [iter %d]\n", cur_iter);
        goto out;
    }
    log_msg("[binradar] [commit] [iter %d] [groups %u] [patches %u] "
            "[bytes %u]\n", cur_iter, group_count, result_count,
            payload->len);
    ok = true;

out:
    if (payload != NULL) g_byte_array_free(payload, TRUE);
    for (uint32_t patch = 0; patch <= manager->patch_max_id; patch++) {
        if (members[patch] != NULL) g_array_free(members[patch], TRUE);
    }
    g_free(members);
    if (ok) {
        /* The attempted sweep is now canonical evidence: only now may its
         * staged feedback pairs become committed sweep evidence.  Failure is
         * fatal to the phase and rolls back every moved pair. */
        ok = binradar_cache_feedback_publish(manager);
        if (ok) binradar_cache_clear_iteration(manager);
    }
    return ok;
}

PatchedResult *binradar_cache_result(BinradarManager *manager,
                                     uint32_t patch_id)
{
    if (manager == NULL || manager->current == NULL ||
        patch_id > manager->patch_max_id) {
        log_msg("[binradar] [invalid-result] [patch %u]\n", patch_id);
        exit(EXIT_FAILURE);
    }
    return &manager->current->patch_results[patch_id];
}

static void binradar_manager_handle_patch_line(BinradarManager *manager, const char *line) {
    sbsv_row *row = NULL;
    log_msg("[binradar] [patch-res] %s\n", line);
    sbsv_parser_parse_line_detached(manager->patch_result_parser, line, 0, &row);
    int cur_iter = binradar_cache_iteration(manager, -1);
    if (row != NULL) {
        if (strcmp(sbsv_row_schema_name(row), "patch") == 0) {
            // Process patch row
            long long patch_id = sbsv_row_get_int(row, "id", NULL);
            long long br = sbsv_row_get_int(row, "br", NULL);
            long long iter = sbsv_row_get_int(row, "v", NULL);
            if (iter != cur_iter) {
                log_msg("[binradar] [iter-mismatch] [v %lld] [iter %d] [id %lld] [br %lld]\n", iter, cur_iter, patch_id, br);
                sbsv_row_free(row);
                return;
            }
            if (patch_id < 0 || patch_id > UINT32_MAX) {
                log_msg("[binradar] [invalid-patch-id] [id %lld]\n", patch_id);
                sbsv_row_free(row);
                return;
            }
            PatchedResult *result = binradar_cache_result(
                manager, (uint32_t)patch_id);
            if (result->br_taken == NULL) {
                result->br_taken = g_array_new(FALSE, FALSE, sizeof(int));
            }
            int br_taken = (int)br;
            g_array_append_val(result->br_taken, br_taken);
        }
        sbsv_row_free(row);
    }
}

static void binradar_manager_handle_patch_bytes(BinradarManager *manager, const char *buf, size_t len) {
    for (size_t i = 0; i < len; i++) {
        char c = buf[i];

        if (manager->line_idx + 1 >= sizeof(manager->line_buf)) {
            // Line too long, reset buffer
            manager->line_buf[manager->line_idx] = '\0';
            binradar_manager_handle_patch_line(manager, manager->line_buf);
            manager->line_idx = 0;
        }

        manager->line_buf[manager->line_idx++] = c;

        if (c == '\n') {
            manager->line_buf[manager->line_idx - 1] = '\0';
            binradar_manager_handle_patch_line(manager, manager->line_buf);
            manager->line_idx = 0;
        }
    }
}

void binradar_cache_drain_patch(BinradarManager *manager) {
    char buf[4096];
    for (;;) {
        ssize_t n = read(manager->patch_fd_r, buf, sizeof(buf));
        if (n > 0) {
            binradar_manager_handle_patch_bytes(manager, buf, (size_t)n);
            continue;
        }
        if (n == 0) {
            // write end closed
            break;
        }
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
            break;
        }
        if (errno == EINTR) {
            continue;
        }
        break;
    }
}

void binradar_cache_drain_capture(BinradarManager *manager) {
    uint8_t buf[8192];
    if (manager == NULL || manager->cache_fd_r < 0) return;
    for (;;) {
        ssize_t n = read(manager->cache_fd_r, buf, sizeof(buf));
        if (n > 0) {
            if (!manager->cache_capture_overflow &&
                (size_t)n <= BRCACHE_MAX_CAPTURE_BYTES -
                             manager->cache_bytes->len) {
                g_byte_array_append(manager->cache_bytes, buf, (guint)n);
            } else {
                manager->cache_capture_overflow = true;
            }
            continue;
        }
        if (n == 0 || errno == EAGAIN || errno == EWOULDBLOCK) break;
        if (errno == EINTR) continue;
        manager->cache_capture_overflow = true;
        break;
    }
}

void binradar_cache_reset_child(BinradarManager *manager) {
    if (manager == NULL) return;
    manager->line_idx = 0;
    memset(manager->line_buf, 0, sizeof(manager->line_buf));
    if (manager->cache_bytes != NULL) {
        g_byte_array_set_size(manager->cache_bytes, 0);
    }
    manager->cache_capture_overflow = false;
}


typedef struct BinradarExprParser {
    const char *cursor;
    GArray *nodes;
    uint32_t depth;
} BinradarExprParser;

static bool binradar_parse_u64(const char **cursor, uint64_t *value)
{
    const char *p = *cursor;
    uint64_t result = 0;
    if (*p < '0' || *p > '9') return false;
    do {
        uint32_t digit = (uint32_t)(*p - '0');
        if (result > (UINT64_MAX - digit) / 10u) return false;
        result = result * 10u + digit;
        p++;
    } while (*p >= '0' && *p <= '9');
    *cursor = p;
    *value = result;
    return true;
}

static bool binradar_parse_expr(BinradarExprParser *parser,
                                uint32_t *index_out)
{
    BinradarExprNode node = {0};
    uint64_t number;
    char op;
    if (parser->depth++ >= BRCACHE_MAX_EXPR_DEPTH ||
        *parser->cursor == '\0') {
        parser->depth--;
        return false;
    }
    op = *parser->cursor++;
    if (op == 'p' || op == 'n' || op == 'v') {
        if (!binradar_parse_u64(&parser->cursor, &number)) goto invalid;
        if (op == 'v') {
            if (number > 15) goto invalid;
            node.op = BRCACHE_EXPR_VARIABLE;
            node.variable = (uint16_t)number;
        } else {
            node.op = BRCACHE_EXPR_LITERAL;
            node.literal = (int64_t)(op == 'n' ? 0u - number : number);
        }
    } else if (op == '~') {
        node.op = BRCACHE_EXPR_NOT;
        if (!binradar_parse_expr(parser, &node.left)) goto invalid;
    } else {
        switch (op) {
        case '=': node.op = BRCACHE_EXPR_EQ; break;
        case '!': node.op = BRCACHE_EXPR_NE; break;
        case '>':
            node.op = *parser->cursor == '=' ? BRCACHE_EXPR_GE
                                              : BRCACHE_EXPR_GT;
            if (*parser->cursor == '=') parser->cursor++;
            break;
        case '<':
            node.op = *parser->cursor == '=' ? BRCACHE_EXPR_LE
                                              : BRCACHE_EXPR_LT;
            if (*parser->cursor == '=') parser->cursor++;
            break;
        case '+': node.op = BRCACHE_EXPR_ADD; break;
        case '-': node.op = BRCACHE_EXPR_SUB; break;
        case '*': node.op = BRCACHE_EXPR_MUL; break;
        case '/': node.op = BRCACHE_EXPR_DIV; break;
        case '%': node.op = BRCACHE_EXPR_REM; break;
        case '&': node.op = BRCACHE_EXPR_AND; break;
        case '|': node.op = BRCACHE_EXPR_OR; break;
        case '^': node.op = BRCACHE_EXPR_XOR; break;
        case 'l': node.op = BRCACHE_EXPR_SHL; break;
        case 'r': node.op = BRCACHE_EXPR_SHR; break;
        default: goto invalid;
        }
        if (!binradar_parse_expr(parser, &node.left) ||
            !binradar_parse_expr(parser, &node.right)) goto invalid;
    }
    g_array_append_val(parser->nodes, node);
    *index_out = parser->nodes->len - 1;
    parser->depth--;
    return true;
invalid:
    parser->depth--;
    return false;
}

static bool binradar_parse_generic_predicate(BinradarCachePredicate *predicate,
                                             const char *descriptor)
{
    BinradarExprParser parser = {0};
    parser.cursor = descriptor;
    parser.nodes = g_array_new(FALSE, FALSE, sizeof(BinradarExprNode));
    if (!binradar_parse_expr(&parser, &predicate->expr_root) ||
        *parser.cursor != '\0') {
        g_array_free(parser.nodes, TRUE);
        return false;
    }
    predicate->expr_nodes = parser.nodes;
    return true;
}

static bool binradar_parse_decimal_u32(const char **cursor, uint32_t *value)
{
    uint64_t parsed;
    if (!binradar_parse_u64(cursor, &parsed) || parsed > UINT32_MAX) {
        return false;
    }
    *value = (uint32_t)parsed;
    return true;
}

static bool binradar_parse_cwe_predicate(BinradarCachePredicate *predicate,
                                         const char *descriptor)
{
    const char *p = descriptor;
    uint32_t value;
    if (p[0] != 'c' || (p[1] != '1' && p[1] != '2')) return false;
    predicate->cwe_kind = (uint8_t)(p[1] - '0');
    p += 2;
    if (*p == 'p') {
        p++;
        predicate->cell_kind = BRCACHE_CELL_REGISTER;
        if (!binradar_parse_decimal_u32(&p, &value) || value > 15) {
            return false;
        }
        predicate->cell_index = value;
    } else if (*p == 's') {
        p++;
        if (!binradar_parse_decimal_u32(&p, &value) || *p++ != 'i') {
            return false;
        }
        switch (value) {
        case 8: predicate->cell_kind = BRCACHE_CELL_STACK8; break;
        case 16: predicate->cell_kind = BRCACHE_CELL_STACK16; break;
        case 32: predicate->cell_kind = BRCACHE_CELL_STACK32; break;
        case 64: predicate->cell_kind = BRCACHE_CELL_STACK64; break;
        default: return false;
        }
        if (!binradar_parse_decimal_u32(&p, &predicate->cell_index)) {
            return false;
        }
    } else {
        return false;
    }
    if (predicate->cwe_kind == 1) {
        if (predicate->cell_kind != BRCACHE_CELL_REGISTER &&
            predicate->cell_kind != BRCACHE_CELL_STACK64) return false;
        predicate->scale = 1;
    } else {
        if (predicate->cell_kind == BRCACHE_CELL_STACK64 || *p++ != 'q' ||
            !binradar_parse_decimal_u32(&p, &value) ||
            (value != 1 && value != 2 && value != 4 && value != 8)) {
            return false;
        }
        predicate->scale = (uint8_t)value;
    }
    return *p == '\0';
}

static bool binradar_qnum_positive_u32(QObject *obj, uint32_t *value)
{
    QNum *number = qobject_to(QNum, obj);
    uint64_t parsed;
    if (number == NULL || !qnum_get_try_uint(number, &parsed) ||
        parsed == 0 || parsed > UINT32_MAX) return false;
    *value = (uint32_t)parsed;
    return true;
}

bool binradar_cache_load_manifest(BinradarManager *manager,
                                           const char *path)
{
    gchar *content = NULL;
    gsize content_len = 0;
    GError *file_error = NULL;
    Error *json_error = NULL;
    QObject *root = NULL;
    bool ok = false;
    size_t max_descriptor = 0;

    if (!g_file_get_contents(path, &content, &content_len, &file_error)) {
        log_msg("[binradar] [cache-manifest] [error %s]\n",
                file_error != NULL ? file_error->message : "read failed");
        goto out;
    }
    root = qobject_from_json_with_token_limit(
        content, BRCACHE_MAX_MANIFEST_TOKENS, &json_error);
    if (root == NULL) {
        goto out;
    }
    QDict *dict = qobject_to(QDict, root);
    if (dict == NULL || qdict_get_try_int(dict, "version", -1) != 1) {
        log_msg("[binradar] [cache-manifest] [error invalid-version]\n");
        goto out;
    }
    const char *kind = qdict_get_try_str(dict, "kind");
    if (kind != NULL && strcmp(kind, "generic-erm") == 0) {
        manager->cache_family = BRCACHE_FAMILY_GENERIC;
    } else if (kind != NULL && strcmp(kind, "CWE805-erm") == 0) {
        manager->cache_family = BRCACHE_FAMILY_CWE805;
    } else {
        log_msg("[binradar] [cache-manifest] [error invalid-family]\n");
        goto out;
    }
    QList *rows = qobject_to(QList, qdict_get(dict, "predicates"));
    if (rows == NULL || qlist_size(rows) > UINT32_MAX - 1u) {
        log_msg("[binradar] [cache-manifest] [error invalid-predicates]\n");
        goto out;
    }
    manager->cache_predicate_count = (uint32_t)qlist_size(rows);
    manager->cache_predicates = g_new0(BinradarCachePredicate,
                                       manager->cache_predicate_count + 1u);
    const QListEntry *entry;
    uint32_t expected_id = 1;
    QLIST_FOREACH_ENTRY(rows, entry) {
        QDict *row = qobject_to(QDict, qlist_entry_obj(entry));
        uint32_t id, source_line;
        if (row == NULL ||
            !binradar_qnum_positive_u32(qdict_get(row, "id"), &id) ||
            id != expected_id ||
            !binradar_qnum_positive_u32(qdict_get(row, "source_line"),
                                        &source_line)) {
            log_msg("[binradar] [cache-manifest] [error invalid-row] "
                    "[index %u]\n", expected_id);
            goto out;
        }
        const char *descriptor = qdict_get_try_str(row, "descriptor");
        size_t descriptor_len = descriptor != NULL ? strlen(descriptor) : 0;
        if (descriptor_len == 0 || descriptor_len > BRCACHE_MAX_DESCRIPTOR) {
            log_msg("[binradar] [cache-manifest] [error descriptor-size] "
                    "[id %u]\n", id);
            goto out;
        }
        BinradarCachePredicate *predicate = &manager->cache_predicates[id];
        predicate->descriptor = g_strdup(descriptor);
        bool parsed = manager->cache_family == BRCACHE_FAMILY_GENERIC
            ? binradar_parse_generic_predicate(predicate, descriptor)
            : binradar_parse_cwe_predicate(predicate, descriptor);
        if (!parsed) {
            log_msg("[binradar] [cache-manifest] [error descriptor-grammar] "
                    "[id %u]\n", id);
            goto out;
        }
        max_descriptor = MAX(max_descriptor, descriptor_len);
        expected_id++;
    }
    for (uint32_t i = 0; i < manager->patch_cnt; i++) {
        uint32_t id = manager->patch_list != NULL ? manager->patch_list[i]
                                                  : i + 1u;
        if (id == 0 || id > manager->cache_predicate_count ||
            manager->cache_predicates[id].descriptor == NULL) {
            log_msg("[binradar] [cache-manifest] [error missing-active-id] "
                    "[id %u]\n", id);
            goto out;
        }
    }
    manager->selector_size = offsetof(BinradarPatchSelector, descriptor) +
                             max_descriptor + 1u;
    if (manager->selector_size < sizeof(BinradarPatchSelector)) {
        manager->selector_size = sizeof(BinradarPatchSelector);
    }
    ok = true;
    log_msg("[binradar] [cache-manifest] [loaded] [family %s] "
            "[predicates %u] [selector-size %zu]\n", kind,
            manager->cache_predicate_count, manager->selector_size);
out:
    if (json_error != NULL) {
        log_msg("[binradar] [cache-manifest] [json-error %s]\n",
                error_get_pretty(json_error));
        error_free(json_error);
    }
    if (file_error != NULL) g_error_free(file_error);
    qobject_unref(root);
    g_free(content);
    return ok;
}

static void binradar_manager_install_filter(BinradarManager *manager,
                                             GArray *ids,
                                             const char *path)
{
    if (ids->len == 0) {
        log_msg("[binradar] [patch-filter] [no-survivors] [file %s]\n", path);
        manager->patch_cnt = 0;
        manager->patch_max_id = 0;
        return;
    }
    manager->patch_list = g_new(uint32_t, ids->len);
    uint32_t max_id = 0;
    for (guint i = 0; i < ids->len; i++) {
        uint32_t patch = g_array_index(ids, uint32_t, i);
        manager->patch_list[i] = patch;
        max_id = MAX(max_id, patch);
    }
    manager->patch_cnt = ids->len;
    manager->patch_max_id = max_id;
    log_msg("[binradar] [patch-filter] [file %s] [cnt %u] [max-id %u]\n",
            path, manager->patch_cnt, manager->patch_max_id);
}

static bool binradar_manager_load_filter_binary(BinradarManager *manager,
                                                 const char *path,
                                                 const uint8_t *data,
                                                 size_t size)
{
    if (size < BR_EVIDENCE_HEADER_SIZE + BR_EVIDENCE_FRAME_HEADER_SIZE + 4u ||
        memcmp(data, BR_EVIDENCE_MAGIC, 8) != 0 ||
        br_evidence_read_u16(data + 8) != BR_EVIDENCE_VERSION ||
        br_evidence_read_u16(data + 10) != BR_EVIDENCE_KIND_FILTER ||
        br_evidence_read_u32(data + 12) != 0) {
        return false;
    }
    const uint8_t *frame = data + BR_EVIDENCE_HEADER_SIZE;
    uint32_t length = br_evidence_read_u32(frame);
    uint16_t type = br_evidence_read_u16(frame + 4);
    uint16_t flags = br_evidence_read_u16(frame + 6);
    size_t expected_size = BR_EVIDENCE_HEADER_SIZE +
        BR_EVIDENCE_FRAME_HEADER_SIZE + (size_t)length + 4u;
    if (length > BR_EVIDENCE_MAX_FRAME || expected_size != size ||
        type != BR_EVIDENCE_RECORD_FILTER || flags != 0 || length < 12u) {
        return false;
    }
    const uint8_t *payload = frame + BR_EVIDENCE_FRAME_HEADER_SIZE;
    uint32_t expected_crc = br_evidence_read_u32(payload + length);
    if (br_evidence_frame_crc(type, flags, payload, length) != expected_crc) {
        return false;
    }
    uint32_t total = br_evidence_read_u32(payload);
    uint32_t passed = br_evidence_read_u32(payload + 4);
    uint32_t bitmap_size = br_evidence_read_u32(payload + 8);
    if (total == UINT32_MAX ||
        (uint64_t)bitmap_size != ((uint64_t)total + 7u) / 8u ||
        length != 12u + bitmap_size) {
        return false;
    }
    const uint8_t *bitmap = payload + 12;
    if (total % 8u != 0 && bitmap_size > 0 &&
        (bitmap[bitmap_size - 1u] >> (total % 8u)) != 0) {
        return false;
    }
    GArray *ids = g_array_sized_new(FALSE, FALSE, sizeof(uint32_t), passed);
    for (uint32_t patch = 1; patch <= total; patch++) {
        if (bitmap[(patch - 1u) / 8u] & (1u << ((patch - 1u) % 8u))) {
            g_array_append_val(ids, patch);
        }
    }
    if (ids->len != passed || passed != manager->patch_cnt) {
        g_array_free(ids, TRUE);
        return false;
    }
    binradar_manager_install_filter(manager, ids, path);
    g_array_free(ids, TRUE);
    return true;
}

bool binradar_cache_load_filter(BinradarManager *manager,
                                const char *path)
{
    gchar *contents = NULL;
    gsize size = 0;
    if (!g_file_get_contents(path, &contents, &size, NULL)) {
        log_msg("[binradar] [patch-filter] [error read] [file %s]\n", path);
        return false;
    }
    if (size >= 8 && memcmp(contents, BR_EVIDENCE_MAGIC, 8) == 0) {
        bool ok = binradar_manager_load_filter_binary(
            manager, path, (const uint8_t *)contents, size);
        g_free(contents);
        if (!ok) {
            log_msg("[binradar] [patch-filter] [error binary] [file %s]\n",
                    path);
            return false;
        }
        return true;
    }
    g_free(contents);

    FILE *fp = fopen(path, "r");
    if (fp == NULL) {
        log_msg("[binradar] [patch-filter] [error open] [file %s]\n", path);
        return false;
    }
    sbsv_parser *parser = sbsv_parser_new(SBSV_PARSER_DEFAULT);
    sbsv_parser_add_schema(parser, "[patch] [id: int] [pass: bool]");
    sbsv_status status = sbsv_parser_load_file(parser, fp);
    fclose(fp);
    if (status != SBSV_OK) {
        log_msg("[binradar] [patch-filter] [error parse] [file %s] "
                "[status %s]\n", path, sbsv_status_str(status));
        sbsv_parser_free(parser);
        return false;
    }
    const sbsv_row **rows = NULL;
    size_t count = 0;
    if (sbsv_parser_get_rows(parser, "patch", &rows, &count) != SBSV_OK) {
        sbsv_parser_free(parser);
        return false;
    }
    GArray *ids = g_array_new(FALSE, FALSE, sizeof(uint32_t));
    for (size_t i = 0; i < count; i++) {
        long long id = sbsv_row_get_int(rows[i], "id", NULL);
        int pass = sbsv_row_get_bool(rows[i], "pass", NULL);
        if (pass && id > 0 && (uint64_t)id <= UINT32_MAX) {
            uint32_t patch = (uint32_t)id;
            g_array_append_val(ids, patch);
        }
    }
    sbsv_free_row_ref_array(rows);
    sbsv_parser_free(parser);
    if (ids->len != manager->patch_cnt) {
        g_array_free(ids, TRUE);
        log_msg("[binradar] [patch-filter] [error count] [file %s]\n", path);
        return false;
    }
    binradar_manager_install_filter(manager, ids, path);
    g_array_free(ids, TRUE);
    return true;
}


static int64_t binradar_shift_right(int64_t value, int64_t amount)
{
    if (amount >= 64) return value < 0 ? -1 : 0;
    if (amount <= -64) return 0;
    if (amount < 0) return (int64_t)((uint64_t)value << (uint64_t)-amount);
    if (amount == 0) return value;
    uint64_t bits = (uint64_t)value >> (uint64_t)amount;
    if (value < 0) bits |= ~(uint64_t)0 << (64u - (uint64_t)amount);
    return (int64_t)bits;
}

static int64_t binradar_shift_left(int64_t value, int64_t amount)
{
    if (amount >= 64) return 0;
    if (amount <= -64) return value < 0 ? -1 : 0;
    if (amount < 0) return binradar_shift_right(value, -amount);
    return (int64_t)((uint64_t)value << (uint64_t)amount);
}

static bool binradar_eval_expr(const BinradarCachePredicate *predicate,
                               uint32_t index, const uint64_t regs[16],
                               int64_t *value, bool *crashed)
{
    if (predicate->expr_nodes == NULL ||
        index >= predicate->expr_nodes->len) return false;
    const BinradarExprNode *node = &g_array_index(
        predicate->expr_nodes, BinradarExprNode, index);
    int64_t left = 0, right = 0;
    if (node->op == BRCACHE_EXPR_LITERAL) {
        *value = node->literal;
        return true;
    }
    if (node->op == BRCACHE_EXPR_VARIABLE) {
        *value = (int64_t)regs[node->variable];
        return true;
    }
    if (!binradar_eval_expr(predicate, node->left, regs, &left, crashed)) {
        return false;
    }
    if (node->op == BRCACHE_EXPR_NOT) {
        *value = ~left;
        return true;
    }
    if (!binradar_eval_expr(predicate, node->right, regs, &right, crashed)) {
        return false;
    }
    switch (node->op) {
    case BRCACHE_EXPR_EQ: *value = left == right; break;
    case BRCACHE_EXPR_NE: *value = left != right; break;
    case BRCACHE_EXPR_GT: *value = left > right; break;
    case BRCACHE_EXPR_GE: *value = left >= right; break;
    case BRCACHE_EXPR_LT: *value = left < right; break;
    case BRCACHE_EXPR_LE: *value = left <= right; break;
    case BRCACHE_EXPR_ADD:
        *value = (int64_t)((uint64_t)left + (uint64_t)right); break;
    case BRCACHE_EXPR_SUB:
        *value = (int64_t)((uint64_t)left - (uint64_t)right); break;
    case BRCACHE_EXPR_MUL:
        *value = (int64_t)((uint64_t)left * (uint64_t)right); break;
    case BRCACHE_EXPR_DIV:
        if (right == 0 || (left == INT64_MIN && right == -1)) {
            *crashed = true;
            *value = 0;
        } else {
            *value = left / right;
        }
        break;
    case BRCACHE_EXPR_REM:
        if (right == 0 || (left == INT64_MIN && right == -1)) {
            *crashed = true;
            *value = 0;
        } else {
            *value = left % right;
        }
        break;
    case BRCACHE_EXPR_AND: *value = left & right; break;
    case BRCACHE_EXPR_OR: *value = left | right; break;
    case BRCACHE_EXPR_XOR: *value = left ^ right; break;
    case BRCACHE_EXPR_SHL: *value = binradar_shift_left(left, right); break;
    case BRCACHE_EXPR_SHR: *value = binradar_shift_right(left, right); break;
    default: return false;
    }
    return true;
}

typedef struct BinradarCacheClamp {
    uint64_t begin;
    uint64_t end;
} BinradarCacheClamp;

static bool binradar_cache_read_cell(const BinradarCachePredicate *predicate,
                                     const uint64_t regs[16],
                                     const uint8_t *stack, size_t stack_size,
                                     uint64_t *value)
{
    if (predicate->cell_kind == BRCACHE_CELL_REGISTER) {
        *value = regs[predicate->cell_index];
        return true;
    }
    size_t width = predicate->cell_kind == BRCACHE_CELL_STACK8 ? 1u :
                   predicate->cell_kind == BRCACHE_CELL_STACK16 ? 2u :
                   predicate->cell_kind == BRCACHE_CELL_STACK32 ? 4u : 8u;
    if (predicate->cell_index > SIZE_MAX / width) return false;
    size_t offset = (size_t)predicate->cell_index * width;
    if (offset > stack_size || width > stack_size - offset) return false;
    *value = 0;
    memcpy(value, stack + offset, width);
    return true;
}

static bool binradar_eval_cache_predicate(
        const BinradarManager *manager, uint32_t patch_id,
        const uint64_t regs[16], const BinradarCacheClamp *clamps,
        const uint8_t *stack, size_t stack_size, int *branch)
{
    if (patch_id == 0) {
        *branch = 0;
        return true;
    }
    if (patch_id > manager->cache_predicate_count) return false;
    const BinradarCachePredicate *predicate =
        &manager->cache_predicates[patch_id];
    if (manager->cache_family == BRCACHE_FAMILY_GENERIC) {
        int64_t value = 0;
        bool crashed = false;
        if (!binradar_eval_expr(predicate, predicate->expr_root, regs,
                                &value, &crashed)) return false;
        *branch = crashed ? 2 : value != 0;
        return true;
    }
    uint64_t value;
    if (clamps == NULL ||
        !binradar_cache_read_cell(predicate, regs, stack, stack_size,
                                  &value)) return false;
    if (predicate->cwe_kind == 2) {
        if (value > UINT64_MAX / predicate->scale) {
            *branch = 2;
            return true;
        }
        value *= predicate->scale;
    }
    for (size_t i = 256; i-- > 0;) {
        if (predicate->cwe_kind == 1) {
            if (value >= clamps[i].begin && value < clamps[i].end) {
                *branch = 0;
                return true;
            }
        } else if (value < clamps[i].end - clamps[i].begin) {
            *branch = 0;
            return true;
        }
    }
    *branch = 1;
    return true;
}

bool binradar_cache_vector(BinradarManager *manager,
                                  uint32_t selected_patch,
                                  uint32_t evaluated_patch,
                                  GArray **vector_out)
{
    GArray *vector = g_array_new(FALSE, FALSE, sizeof(int));
    size_t offset = 0;
    uint64_t expected_flags = manager->cache_family == BRCACHE_FAMILY_CWE805
        ? BRCACHE_FLAG_CWE805 : 0;
    size_t expected_record = sizeof(BinradarSnapshotHeader) +
                             16u * sizeof(uint64_t);
    if (manager->cache_family == BRCACHE_FAMILY_CWE805) {
        expected_record += 256u * sizeof(BinradarCacheClamp) +
                           manager->cache_stack_size;
    }
    while (offset < manager->cache_bytes->len) {
        if (manager->cache_bytes->len - offset <
            sizeof(BinradarSnapshotHeader)) goto invalid;
        BinradarSnapshotHeader header;
        memcpy(&header, manager->cache_bytes->data + offset, sizeof(header));
        if (header.magic != BRCACHE_SNAPSHOT_MAGIC ||
            header.version != BRCACHE_SNAPSHOT_VERSION ||
            header.patch_id != selected_patch || header.branch > 2 ||
            header.flags != expected_flags ||
            header.stack_size !=
                (manager->cache_family == BRCACHE_FAMILY_CWE805
                    ? manager->cache_stack_size : 0) ||
            expected_record > manager->cache_bytes->len - offset) {
            goto invalid;
        }
        const uint8_t *payload = manager->cache_bytes->data + offset +
                                 sizeof(header);
        BinradarCacheClamp clamps_storage[256];
        const BinradarCacheClamp *clamps = NULL;
        if (manager->cache_family == BRCACHE_FAMILY_CWE805) {
            memcpy(clamps_storage, payload, sizeof(clamps_storage));
            clamps = clamps_storage;
            payload += sizeof(clamps_storage);
        }
        uint64_t regs[16];
        memcpy(regs, payload, sizeof(regs));
        payload += sizeof(regs);
        int evaluated;
        if (!binradar_eval_cache_predicate(
                manager, evaluated_patch, regs, clamps, payload,
                manager->cache_family == BRCACHE_FAMILY_CWE805
                    ? manager->cache_stack_size : 0,
                &evaluated)) goto invalid;
        if (evaluated_patch == selected_patch &&
            evaluated != (int)header.branch) goto invalid;
        g_array_append_val(vector, evaluated);
        offset += expected_record;
    }
    *vector_out = vector;
    return true;
invalid:
    g_array_free(vector, TRUE);
    return false;
}

bool binradar_cache_vectors_equal(const GArray *left,
                                          const GArray *right)
{
    if (left == NULL || right == NULL || left->len != right->len) return false;
    for (guint i = 0; i < left->len; i++) {
        if (g_array_index(left, int, i) != g_array_index(right, int, i)) {
            return false;
        }
    }
    return true;
}

/* A child normally replays from the entry of the function containing
 * PATCH_LOC and reaches the cached dest() action.  A mutation can still divert
 * control before PATCH_LOC; then no text row is written and br_taken remains
 * NULL.  The corresponding capture vector is empty because neither channel
 * observed a patch-site branch.  Keep the committed value NULL -- .brpatched
 * and FINAL encode that honest no-observation state as `[br null]`; publishing
 * an empty array would produce the invalid SBSV token `[br ]`. */
bool binradar_cache_observed_matches(const GArray *observed,
                                             const GArray *other)
{
    if (observed == NULL) return other != NULL && other->len == 0;
    return binradar_cache_vectors_equal(observed, other);
}

