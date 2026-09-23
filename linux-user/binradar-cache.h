#ifndef BINRADAR_CACHE_H
#define BINRADAR_CACHE_H

#include "snapshot-mutation.h"
#include "snapshot-observation.h"
#include "sbsv.h"

#define BRCACHE_SNAPSHOT_MAGIC 0x48435242u
#define BRCACHE_SNAPSHOT_VERSION 1u
#define BRCACHE_FLAG_TRUNCATED 1u
#define BRCACHE_FLAG_CWE805 2u
#define BRCACHE_FLAG_INVALID 4u
#define BRCACHE_MAX_CAPTURE_BYTES (64u * 1024u * 1024u)
#define BRCACHE_MAX_MANIFEST_TOKENS (4ULL << 20)
#define BRCACHE_MAX_DESCRIPTOR 4095u
#define BRCACHE_MAX_EXPR_DEPTH 256u

typedef struct PatchedResult {
    uint32_t patch_id;
    uint32_t representative;
    GArray *br_taken;
    bool is_crash;
    bool fault_reference_valid;
    SnapshotFaultReferenceSource fault_reference_source;
    uint64_t fault_loc;
} PatchedResult;

typedef struct BinradarResult {
    uint32_t iter;
    PatchedResult *patch_results;
} BinradarResult;

typedef enum BinradarCacheFamily {
    BRCACHE_FAMILY_NONE,
    BRCACHE_FAMILY_GENERIC,
    BRCACHE_FAMILY_CWE805,
} BinradarCacheFamily;

typedef enum BinradarExprOp {
    BRCACHE_EXPR_LITERAL,
    BRCACHE_EXPR_VARIABLE,
    BRCACHE_EXPR_NOT,
    BRCACHE_EXPR_EQ,
    BRCACHE_EXPR_NE,
    BRCACHE_EXPR_GT,
    BRCACHE_EXPR_GE,
    BRCACHE_EXPR_LT,
    BRCACHE_EXPR_LE,
    BRCACHE_EXPR_ADD,
    BRCACHE_EXPR_SUB,
    BRCACHE_EXPR_MUL,
    BRCACHE_EXPR_DIV,
    BRCACHE_EXPR_REM,
    BRCACHE_EXPR_AND,
    BRCACHE_EXPR_OR,
    BRCACHE_EXPR_XOR,
    BRCACHE_EXPR_SHL,
    BRCACHE_EXPR_SHR,
} BinradarExprOp;

typedef struct BinradarExprNode {
    BinradarExprOp op;
    uint32_t left;
    uint32_t right;
    uint16_t variable;
    int64_t literal;
} BinradarExprNode;

typedef enum BinradarCacheCellKind {
    BRCACHE_CELL_REGISTER,
    BRCACHE_CELL_STACK8,
    BRCACHE_CELL_STACK16,
    BRCACHE_CELL_STACK32,
    BRCACHE_CELL_STACK64,
} BinradarCacheCellKind;

typedef struct BinradarCachePredicate {
    char *descriptor;
    GArray *expr_nodes;
    uint32_t expr_root;
    uint8_t cwe_kind;
    BinradarCacheCellKind cell_kind;
    uint32_t cell_index;
    uint8_t scale;
} BinradarCachePredicate;

typedef struct BinradarPatchSelector {
    uint32_t patch_id;
    uint32_t iteration;
    uint32_t descriptor_length;
    uint32_t descriptor_capacity;
    char descriptor[];
} BinradarPatchSelector;

typedef struct BinradarSnapshotHeader {
    uint32_t magic;
    uint32_t version;
    uint32_t patch_id;
    uint32_t branch;
    uint64_t stack_size;
    uint64_t flags;
} BinradarSnapshotHeader;

_Static_assert(sizeof(BinradarSnapshotHeader) == 32,
               "cached snapshot header layout changed");
_Static_assert(offsetof(BinradarPatchSelector, descriptor) == 16,
               "cached selector prefix changed");

typedef struct BinradarManager {
    uint32_t patch_cnt;
    int patch_fd_r;
    uint32_t *cur_patch_id;
    uint32_t *cur_iter;
    sbsv_parser *patch_result_parser;
    BinradarResult *current;
    FILE *evidence_file;
    size_t line_idx;
    char line_buf[4096];
    uint32_t *patch_list;
    uint32_t patch_max_id;
    bool cache_enabled;
    bool cache_inference_enabled;
    BinradarCacheFamily cache_family;
    BinradarCachePredicate *cache_predicates;
    uint32_t cache_predicate_count;
    uint32_t cache_stack_size;
    int cache_fd_r;
    GByteArray *cache_bytes;
    bool cache_capture_overflow;
    BinradarPatchSelector *selector;
    size_t selector_size;
    char *feedback_dir;
    /* One attempt's feedback pairs are staged here and renamed into
     * ``feedback_dir`` only when the attempt commits, so a discarded attempt
     * never appears as committed sweep evidence. */
    char *feedback_staging_dir;
    GPtrArray *feedback_staged_pairs;
    bool poc_fault_valid;
    SnapshotFaultReferenceSource poc_fault_source;
    target_ulong poc_fault_addr;
} BinradarManager;

/* Borrowed only for one synchronous feedback commit. */
typedef struct BinradarMutationFeedbackView {
    const SnapshotMutationWrite *writes;
    uint32_t write_count;
} BinradarMutationFeedbackView;

BinradarResult *binradar_cache_new_iteration(BinradarManager *manager);
int binradar_cache_patch_id(BinradarManager *manager, int new_patch_id);
int binradar_cache_iteration(BinradarManager *manager, int new_iteration);
int binradar_cache_patch_id_at(const BinradarManager *manager, uint32_t index);
/* Required-result lookup: missing iteration state or an out-of-range patch
 * terminates the parent with EXIT_FAILURE. Never discard invalid patch rows
 * as if their branch observations were absent. */
PatchedResult *binradar_cache_result(BinradarManager *manager,
                                     uint32_t patch_id);
void binradar_cache_disable(BinradarManager *manager, const char *reason);
bool binradar_cache_publish_selector(BinradarManager *manager,
                                     uint32_t patch_id, uint32_t iteration);
void binradar_cache_clear_iteration(BinradarManager *manager);
void binradar_cache_restore_uncovered(BinradarManager *manager,
                                      bool *uncovered, const bool *executed);
void binradar_cache_record_outcome(BinradarManager *manager,
                                   uint32_t patch_id,
                                   const SnapshotExitInfo *outcome);
void binradar_cache_materialize(BinradarManager *manager, uint32_t patch_id,
                                uint32_t representative,
                                const GArray *branches,
                                const SnapshotExitInfo *outcome);
bool binradar_cache_commit(BinradarManager *manager);
/* Publish or drop the feedback pairs staged for the current attempt.  A
 * discarded attempt calls the drop path so its pairs never look committed.
 * Publication returns false after rolling back any files already renamed. */
bool binradar_cache_feedback_publish(BinradarManager *manager);
void binradar_cache_feedback_drop(BinradarManager *manager);
void binradar_cache_feedback_release(BinradarManager *manager);
bool binradar_cache_feedback_write(
    BinradarManager *manager, uint32_t iteration, uint32_t patch_id,
    const GArray *branches, const BinradarMutationFeedbackView *mutation);
void binradar_cache_drain_patch(BinradarManager *manager);
void binradar_cache_drain_capture(BinradarManager *manager);
void binradar_cache_reset_child(BinradarManager *manager);
bool binradar_cache_load_filter(BinradarManager *manager, const char *path);
bool binradar_cache_load_manifest(BinradarManager *manager, const char *path);
bool binradar_cache_vector(BinradarManager *manager,
                           uint32_t selected_patch,
                           uint32_t evaluated_patch, GArray **vector_out);
bool binradar_cache_vectors_equal(const GArray *left, const GArray *right);
bool binradar_cache_observed_matches(const GArray *observed,
                                     const GArray *other);

uint16_t br_evidence_read_u16(const uint8_t *p);
uint32_t br_evidence_read_u32(const uint8_t *p);
uint32_t br_evidence_frame_crc(uint16_t type, uint16_t flags,
                               const uint8_t *payload, size_t len);
bool br_evidence_write_header(FILE *fp, uint16_t kind);

#define BR_EVIDENCE_HEADER_SIZE 16u
#define BR_EVIDENCE_FRAME_HEADER_SIZE 8u
#define BR_EVIDENCE_MAGIC "BRDATAB1"
/* FILTER and VERIFIER payloads keep version 1; BINRADAR evidence is version 2
 * because attempt ids may now have gaps after a discarded attempt. */
#define BR_EVIDENCE_VERSION 1u
#define BR_EVIDENCE_VERSION_BINRADAR 2u
#define BR_EVIDENCE_KIND_FILTER 1u
#define BR_EVIDENCE_KIND_BINRADAR 3u
#define BR_EVIDENCE_RECORD_FILTER 1u
#define BR_EVIDENCE_RECORD_BINRADAR_ITERATION 4u
#define BR_EVIDENCE_MAX_FRAME (256u * 1024u * 1024u)
#define BR_EVIDENCE_GROUP_BRANCH_NULL 1u
#define BR_EVIDENCE_OUTCOME_NORMAL 1u
#define BR_EVIDENCE_OUTCOME_CRASH 2u

#endif /* BINRADAR_CACHE_H */
