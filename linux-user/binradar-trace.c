#include "qemu/osdep.h"
#include "qemu.h"
#include "qemu/selfmap.h"
#include "disas/disas.h"
#include "exec/helper-proto.h"
#include "qemuafl/binradar-trace.h"
#include "qemuafl/qasan-qemu.h"

typedef struct BinradarFrame {
    target_ulong entry;
    target_ulong return_addr;
    bool has_entry;
    bool saw_patch_hit;
} BinradarFrame;

typedef struct BinradarAddrHit {
    target_ulong addr;
    uint64_t hits;
} BinradarAddrHit;

typedef struct BinradarFuncHit {
    target_ulong entry;
    uint64_t hits;
} BinradarFuncHit;

typedef struct BinradarGroup BinradarGroup;
typedef struct BinradarFd BinradarFd;

struct BinradarGroup {
    uint64_t id;
    int64_t offset;
    int refs;
    BinradarGroup *next;
};

struct BinradarFd {
    int fd;
    bool seekable;
    BinradarGroup *group;
    BinradarFd *next;
};

static bool trace_enabled;
static bool trace_basic_blocks;
static bool printed_final;
static bool pending_patch_hit;
static bool patch_covered;
static bool patch_func_entry_covered;
static bool patch_func_entry_hit;
static int64_t start_ms;

static char *input_path;
static char *binary_path;
static const char *asan_mode = "host";
static target_ulong patch_loc;
static target_ulong patch_func_entry;
static target_ulong patch_hit_loc;
static target_ulong target_start;
static target_ulong target_end;
static uint64_t patch_hits;
static uint64_t patch_unknown_hits;
static uint64_t open_hits;
static uint64_t reads_before_patch;
static uint64_t reads_after_patch;
static uint64_t next_group_id = 1;
static target_ulong pending_patch_pc;

static BinradarFrame *frames;
static size_t frames_len;
static size_t frames_cap;
static BinradarAddrHit *basic_blocks;
static size_t basic_blocks_len;
static size_t basic_blocks_cap;
static BinradarFuncHit *func_hits;
static size_t func_hits_len;
static size_t func_hits_cap;
static BinradarFd *fds;
static BinradarGroup *groups;

static int64_t now_ms(void)
{
    return g_get_monotonic_time() / 1000;
}

static int64_t elapsed_ms(void)
{
    if (!start_ms) {
        return 0;
    }
    return now_ms() - start_ms;
}

static void trace_log(const char *fmt, ...)
{
    va_list ap;

    if (!trace_enabled) {
        return;
    }

    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fprintf(stderr, " [time %" PRId64 "]\n", elapsed_ms());
}

static target_ulong parse_addr(const char *value)
{
    return value ? (target_ulong)strtoull(value, NULL, 0) : 0;
}

static void enable_trace(void)
{
    trace_enabled = true;
}

void binradar_trace_init_time(void)
{
    start_ms = now_ms();
}

void binradar_trace_set_input(const char *path)
{
    enable_trace();
    g_free(input_path);
    input_path = g_strdup(path ? path : "");
}

void binradar_trace_set_patch_loc(const char *value)
{
    enable_trace();
    patch_loc = parse_addr(value);
}

void binradar_trace_set_patch_func_entry(const char *value)
{
    enable_trace();
    patch_func_entry = parse_addr(value);
}

void binradar_trace_set_asan(const char *mode)
{
    enable_trace();
    if (mode && (!strcmp(mode, "host") || !strcmp(mode, "guest") || !strcmp(mode, "none"))) {
        asan_mode = mode;
    } else {
        fprintf(stderr, "qemu: invalid --asan mode '%s'\n", mode ? mode : "");
        exit(EXIT_FAILURE);
    }
}

void binradar_trace_ignore_arg(const char *value)
{
    (void)value;
    enable_trace();
}

void binradar_trace_enable_basic_blocks(const char *unused)
{
    (void)unused;
    enable_trace();
    trace_basic_blocks = true;
}

int binradar_trace_is_enabled(void)
{
    return trace_enabled;
}

int binradar_trace_symbols_enabled(void)
{
    return trace_enabled;
}

int binradar_trace_trace_basic_blocks(void)
{
    return trace_enabled && trace_basic_blocks;
}

int binradar_trace_should_hook_pc(target_ulong pc)
{
    if (!trace_enabled) {
        return 0;
    }
    return (patch_hit_loc && pc == patch_hit_loc) ||
           (patch_func_entry && pc == patch_func_entry);
}

int binradar_trace_should_drop_separator(int target_index, const char *arg)
{
    return trace_enabled && target_index == 1 && arg && !strcmp(arg, "--");
}

char *binradar_trace_rewrite_arg(const char *arg)
{
    if (trace_enabled && input_path && arg && !strcmp(arg, "@@")) {
        return g_strdup(input_path);
    }
    return g_strdup(arg ? arg : "");
}

int binradar_trace_suppress_write_fd(int fd)
{
    return trace_enabled && (fd == STDOUT_FILENO || fd == STDERR_FILENO);
}

static void ensure_frames(size_t needed)
{
    if (frames_cap >= needed) {
        return;
    }
    frames_cap = MAX(needed, frames_cap ? frames_cap * 2 : 64);
    frames = g_realloc(frames, frames_cap * sizeof(*frames));
}

static void push_frame(target_ulong entry, bool has_entry, target_ulong return_addr)
{
    ensure_frames(frames_len + 1);
    frames[frames_len++] = (BinradarFrame){
        .entry = entry,
        .return_addr = return_addr,
        .has_entry = has_entry,
        .saw_patch_hit = false,
    };
}

static void reset_runtime(target_ulong root_entry)
{
    frames_len = 0;
    push_frame(root_entry, root_entry != 0, 0);
    patch_hits = 0;
    patch_unknown_hits = 0;
    patch_covered = false;
    patch_func_entry_covered = false;
    patch_func_entry_hit = false;
    func_hits_len = 0;
    basic_blocks_len = 0;
}

static BinradarFuncHit *get_func_hit(target_ulong entry)
{
    size_t i;

    for (i = 0; i < func_hits_len; i++) {
        if (func_hits[i].entry == entry) {
            return &func_hits[i];
        }
    }
    if (func_hits_len == func_hits_cap) {
        func_hits_cap = func_hits_cap ? func_hits_cap * 2 : 16;
        func_hits = g_realloc(func_hits, func_hits_cap * sizeof(*func_hits));
    }
    func_hits[func_hits_len] = (BinradarFuncHit){ .entry = entry, .hits = 0 };
    return &func_hits[func_hits_len++];
}

static BinradarAddrHit *get_addr_hit(BinradarAddrHit **items, size_t *len,
                                     size_t *cap, target_ulong addr)
{
    size_t i;

    for (i = 0; i < *len; i++) {
        if ((*items)[i].addr == addr) {
            return &(*items)[i];
        }
    }
    if (*len == *cap) {
        *cap = *cap ? *cap * 2 : 256;
        *items = g_realloc(*items, *cap * sizeof(**items));
    }
    (*items)[*len] = (BinradarAddrHit){ .addr = addr, .hits = 0 };
    return &(*items)[(*len)++];
}

void binradar_trace_after_load(target_ulong entry, target_ulong start_code,
                               target_ulong end_code, const char *binary)
{
    if (!trace_enabled) {
        return;
    }

    target_start = start_code;
    target_end = end_code;
    g_free(binary_path);
    binary_path = g_strdup(binary ? binary : "");
    patch_hit_loc = patch_loc ? patch_loc : patch_func_entry;

    trace_log("[asan] [mode %s]", asan_mode);
    trace_log("[entry] [address 0x%" PRIx64 "]", (uint64_t)entry);
    if (patch_hit_loc) {
        trace_log("[patch-info] [set true] [location 0x%" PRIx64 "]", (uint64_t)patch_hit_loc);
    } else {
        trace_log("[patch-info] [set false] [location 0]");
    }
    if (patch_func_entry) {
        trace_log("[patch-func-entry] [set] [set true] [location 0x%" PRIx64 "]", (uint64_t)patch_func_entry);
    } else {
        trace_log("[patch-func-entry] [set] [set false] [location 0]");
    }
    trace_log("running %s @ 0x%" PRIx64, binary_path, (uint64_t)entry);
}

void binradar_trace_start(target_ulong pc)
{
    if (!trace_enabled) {
        return;
    }
    reset_runtime(pc);
}

static void record_patch_hit(target_ulong pc)
{
    ssize_t i;
    BinradarFrame *frame = NULL;

    if (!patch_hit_loc || pc != patch_hit_loc) {
        return;
    }

    patch_covered = true;
    patch_hits++;
    for (i = (ssize_t)frames_len - 1; i >= 0; i--) {
        if (frames[i].has_entry) {
            frame = &frames[i];
            break;
        }
    }
    if (frame) {
        if (!frame->saw_patch_hit) {
            get_func_hit(frame->entry)->hits++;
            frame->saw_patch_hit = true;
        }
    } else {
        patch_unknown_hits++;
    }
}

static void flush_pending_patch(void)
{
    if (!pending_patch_hit) {
        return;
    }
    record_patch_hit(pending_patch_pc);
    pending_patch_hit = false;
}

void binradar_trace_record_bb(target_ulong pc)
{
    BinradarAddrHit *hit;

    if (!trace_enabled || !trace_basic_blocks) {
        return;
    }
    flush_pending_patch();
    hit = get_addr_hit(&basic_blocks, &basic_blocks_len, &basic_blocks_cap, pc);
    hit->hits++;
}

void binradar_trace_insn_hit(target_ulong pc)
{
    if (!trace_enabled) {
        return;
    }

    if (patch_hit_loc && pc == patch_hit_loc) {
        pending_patch_hit = true;
        pending_patch_pc = pc;
    }

    if (patch_func_entry && pc == patch_func_entry) {
        patch_func_entry_covered = true;
        patch_func_entry_hit = true;
    }
}

void binradar_trace_call(target_ulong pc, target_ulong return_addr,
                         target_ulong entry)
{
    (void)pc;
    if (!trace_enabled) {
        return;
    }
    if (pending_patch_hit && pending_patch_pc != pc) {
        flush_pending_patch();
    }
    push_frame(entry, entry != 0, return_addr);
    if (pending_patch_hit && pending_patch_pc == pc) {
        flush_pending_patch();
    }
}

void binradar_trace_ret(target_ulong pc, target_ulong return_addr)
{
    (void)pc;
    if (!trace_enabled) {
        return;
    }
    flush_pending_patch();
    while (frames_len > 1) {
        BinradarFrame frame = frames[--frames_len];
        if (frame.return_addr == return_addr) {
            break;
        }
    }
}

static BinradarGroup *new_group(void)
{
    BinradarGroup *group = g_new0(BinradarGroup, 1);

    group->id = next_group_id++;
    group->next = groups;
    group->refs = 0;
    groups = group;
    return group;
}

static BinradarFd *find_fd(int fd)
{
    BinradarFd *cur;

    for (cur = fds; cur; cur = cur->next) {
        if (cur->fd == fd) {
            return cur;
        }
    }
    return NULL;
}

static void remove_fd(int fd)
{
    BinradarFd **link = &fds;

    while (*link) {
        BinradarFd *cur = *link;
        if (cur->fd == fd) {
            *link = cur->next;
            if (cur->group) {
                cur->group->refs--;
            }
            g_free(cur);
            return;
        }
        link = &cur->next;
    }
}

static bool classify_seekable_path(const char *path)
{
    struct stat st;

    if (!path || stat(path, &st) != 0) {
        return false;
    }
    return S_ISREG(st.st_mode) || S_ISDIR(st.st_mode) || S_ISBLK(st.st_mode);
}

static void note_open(int fd, const char *path)
{
    BinradarFd *info;
    BinradarGroup *group;
    bool seekable;

    if (!trace_enabled || !patch_func_entry || fd < 0) {
        return;
    }

    remove_fd(fd);
    seekable = classify_seekable_path(path);
    open_hits++;
    if (!seekable) {
        trace_log("[file-trace] [open] [path %s] [fd %d] [gid 0] [offset 0] [seekable false] [after_patch %s]",
                  path ? path : "", fd, patch_func_entry_hit ? "true" : "false");
        return;
    }

    group = new_group();
    group->refs = 1;
    info = g_new0(BinradarFd, 1);
    info->fd = fd;
    info->seekable = true;
    info->group = group;
    info->next = fds;
    fds = info;
    trace_log("[file-trace] [open] [path %s] [fd %d] [gid %" PRIu64 "] [offset 0] [seekable true] [after_patch %s]",
              path ? path : "", fd, group->id, patch_func_entry_hit ? "true" : "false");
}

static void note_alias(int old_fd, int new_fd, const char *kind, int cmd)
{
    BinradarFd *old_info;
    BinradarFd *info;

    if (!trace_enabled || !patch_func_entry || new_fd < 0) {
        return;
    }
    old_info = find_fd(old_fd);
    if (!old_info || !old_info->group) {
        return;
    }

    remove_fd(new_fd);
    old_info->group->refs++;
    info = g_new0(BinradarFd, 1);
    info->fd = new_fd;
    info->seekable = old_info->seekable;
    info->group = old_info->group;
    info->next = fds;
    fds = info;

    if (!strcmp(kind, "fcntl-dup")) {
        trace_log("[file-trace] [fcntl-dup] [fd %d] [cmd %d] [new_fd %d] [gid %" PRIu64 "] [offset %" PRId64 "] [seekable %s] [after_patch %s]",
                  old_fd, cmd, new_fd, info->group->id, info->group->offset,
                  info->seekable ? "true" : "false", patch_func_entry_hit ? "true" : "false");
    } else {
        trace_log("[file-trace] [dup] [old_fd %d] [new_fd %d] [gid %" PRIu64 "] [offset %" PRId64 "] [seekable %s] [after_patch %s]",
                  old_fd, new_fd, info->group->id, info->group->offset,
                  info->seekable ? "true" : "false", patch_func_entry_hit ? "true" : "false");
    }
}

static void note_close(int fd, abi_long result)
{
    BinradarFd *info;
    uint64_t gid;
    BinradarGroup *group;
    int64_t offset;
    bool seekable;

    if (!trace_enabled || !patch_func_entry) {
        return;
    }
    info = find_fd(fd);
    if (!info || !info->group) {
        return;
    }

    group = info->group;
    gid = group->id;
    offset = group->offset;
    seekable = info->seekable;
    trace_log("[file-trace] [close] [fd %d] [gid %" PRIu64 "] [offset %" PRId64 "] [result %" PRId64 "] [after_patch %s]",
              fd, gid, offset, (int64_t)result, patch_func_entry_hit ? "true" : "false");
    remove_fd(fd);
    if (group->refs <= 0) {
        trace_log("[file-trace] [group-close] [gid %" PRIu64 "] [after_patch %s]",
                  gid, patch_func_entry_hit ? "true" : "false");
    }
    (void)seekable;
}

static void note_lseek(int fd, abi_long offset, abi_long whence, abi_long result)
{
    BinradarFd *info;

    if (!trace_enabled || !patch_func_entry) {
        return;
    }
    info = find_fd(fd);
    if (!info || !info->group) {
        return;
    }
    if (result >= 0) {
        info->group->offset = result;
        trace_log("[file-trace] [lseek] [fd %d] [gid %" PRIu64 "] [offset %" PRId64 "] [whence %" PRId64 "] [new_offset %" PRId64 "] [seekable %s] [succ true] [after_patch %s]",
                  fd, info->group->id, (int64_t)offset, (int64_t)whence,
                  (int64_t)result, info->seekable ? "true" : "false",
                  patch_func_entry_hit ? "true" : "false");
    } else {
        trace_log("[file-trace] [lseek] [fd %d] [gid %" PRIu64 "] [offset %" PRId64 "] [whence %" PRId64 "] [new_offset %" PRId64 "] [seekable %s] [succ false] [after_patch %s]",
                  fd, info->group->id, (int64_t)offset, (int64_t)whence,
                  (int64_t)result, info->seekable ? "true" : "false",
                  patch_func_entry_hit ? "true" : "false");
    }
}

static void note_read(int fd, abi_long bytes)
{
    BinradarFd *info;
    int64_t old_offset;

    if (!trace_enabled || !patch_func_entry || bytes <= 0) {
        return;
    }
    info = find_fd(fd);
    if (!info || !info->group) {
        return;
    }
    old_offset = info->group->offset;
    info->group->offset += bytes;
    if (patch_func_entry_hit) {
        reads_after_patch++;
        trace_log("[file-trace] [read] [syscall %d] [fd %d] [gid %" PRIu64 "] [offset %" PRId64 "] [seekable %s] [bytes %" PRId64 "] [after_patch true]",
                  TARGET_NR_read, fd, info->group->id, old_offset,
                  info->seekable ? "true" : "false", (int64_t)bytes);
    } else {
        reads_before_patch++;
    }
}

void binradar_trace_post_syscall(void *cpu_env, int num, target_long ret,
                                 target_long arg1, target_long arg2,
                                 target_long arg3, target_long arg4,
                                 target_long arg5, target_long arg6)
{
    char *path;

    (void)cpu_env;
    (void)arg5;
    (void)arg6;

    if (!trace_enabled || !patch_func_entry || ret < 0) {
        return;
    }

    switch (num) {
#ifdef TARGET_NR_open
    case TARGET_NR_open:
        path = lock_user_string(arg1);
        if (path) {
            note_open((int)ret, path);
            unlock_user(path, arg1, 0);
        }
        break;
#endif
    case TARGET_NR_openat:
        path = lock_user_string(arg2);
        if (path) {
            note_open((int)ret, path);
            unlock_user(path, arg2, 0);
        }
        break;
    case TARGET_NR_read:
        note_read((int)arg1, ret);
        break;
#ifdef TARGET_NR_lseek
    case TARGET_NR_lseek:
        note_lseek((int)arg1, arg2, arg3, ret);
        break;
#endif
    case TARGET_NR_close:
        note_close((int)arg1, ret);
        break;
    case TARGET_NR_dup:
        note_alias((int)arg1, (int)ret, "dup", 0);
        break;
#ifdef TARGET_NR_dup2
    case TARGET_NR_dup2:
        if (ret == arg2) {
            note_alias((int)arg1, (int)arg2, "dup", 0);
        }
        break;
#endif
#if defined(CONFIG_DUP3) && defined(TARGET_NR_dup3)
    case TARGET_NR_dup3:
        if (ret == arg2) {
            note_alias((int)arg1, (int)arg2, "dup", 0);
        }
        break;
#endif
#ifdef TARGET_NR_fcntl
    case TARGET_NR_fcntl:
        if (arg2 == F_DUPFD
#ifdef F_DUPFD_CLOEXEC
            || arg2 == F_DUPFD_CLOEXEC
#endif
        ) {
            note_alias((int)arg1, (int)ret, "fcntl-dup", (int)arg2);
        }
        break;
#endif
    default:
        break;
    }
}

static char *resolve_addr(target_ulong addr)
{
    GSList *maps, *iter;
    const char *symbol;
    char *ret = NULL;

    symbol = lookup_symbol(addr);
    maps = read_self_maps();
    for (iter = maps; iter; iter = g_slist_next(iter)) {
        MapInfo *e = (MapInfo *)iter->data;
        target_ulong start, end;

        if (!e->path || !e->path[0] || !h2g_valid(e->start)) {
            continue;
        }
        start = h2g(e->start);
        if (e->end == 0 || !h2g_valid(e->end - 1)) {
            continue;
        }
        end = h2g(e->end - 1) + 1;
        if (addr >= start && addr < end) {
            if (symbol && symbol[0]) {
                ret = g_strdup_printf(" in %s (%s+0x%" PRIx64 ")", symbol,
                                      e->path, (uint64_t)addr);
            } else {
                ret = g_strdup_printf(" (%s+0x%" PRIx64 ")", e->path,
                                      (uint64_t)addr);
            }
            break;
        }
    }
    free_self_maps(maps);
    if (!ret) {
        if (symbol && symbol[0]) {
            ret = g_strdup_printf(" in %s", symbol);
        } else {
            ret = g_strdup("");
        }
    }
    return ret;
}

static bool in_target(target_ulong addr)
{
    return target_start && target_end && addr >= target_start && addr < target_end;
}

static int cmp_addr_hit(const void *a, const void *b)
{
    const BinradarAddrHit *aa = a;
    const BinradarAddrHit *bb = b;

    if (aa->addr < bb->addr) {
        return -1;
    }
    return aa->addr > bb->addr;
}

static int cmp_func_hit(const void *a, const void *b)
{
    const BinradarFuncHit *aa = a;
    const BinradarFuncHit *bb = b;

    if (aa->entry < bb->entry) {
        return -1;
    }
    return aa->entry > bb->entry;
}

static void print_stacktrace(target_ulong pc)
{
    size_t idx = 0;
    ssize_t i;
    int fault_idx = -1;
    target_ulong fault_addr = 0;
    char *symbol;

    trace_log("stacktrace:");
    symbol = resolve_addr(pc);
    trace_log("[stacktrace] [idx %zu] [addr 0x%" PRIx64 "] [symbol %s]",
              idx, (uint64_t)pc, symbol);
    g_free(symbol);
    idx++;

    for (i = (ssize_t)frames_len - 1; i >= 0; i--) {
        target_ulong addr = frames[i].return_addr;
        if (!addr) {
            addr = frames[i].entry;
        }
        if (!addr) {
            continue;
        }
        symbol = resolve_addr(addr);
        trace_log("[stacktrace] [idx %zu] [addr 0x%" PRIx64 "] [symbol %s]",
                  idx, (uint64_t)addr, symbol);
        g_free(symbol);
        if (fault_idx < 0 && in_target(addr)) {
            fault_idx = (int)idx;
            fault_addr = addr;
        }
        idx++;
    }

    if (fault_idx < 0 && in_target(pc)) {
        fault_idx = 0;
        fault_addr = pc;
    }

    if (fault_idx >= 0) {
        symbol = resolve_addr(fault_addr);
        trace_log("[fault-addr] [idx %d] [addr 0x%" PRIx64 "] [symbol %s]",
                  fault_idx, (uint64_t)fault_addr, symbol);
        g_free(symbol);
    }
}

static const char *target_signal_name(int sig)
{
    switch (target_to_host_signal(sig)) {
    case SIGABRT:
        return "SIGABRT";
    case SIGBUS:
        return "SIGBUS";
    case SIGFPE:
        return "SIGFPE";
    case SIGILL:
        return "SIGILL";
    case SIGSEGV:
        return "SIGSEGV";
    case SIGTRAP:
        return "SIGTRAP";
    default:
        return "UNKNOWN";
    }
}

static void print_patch_summary(void)
{
    size_t i;

    if (!patch_hit_loc) {
        return;
    }
    trace_log("[patch-cov] [location 0x%" PRIx64 "] [covered %s] [hits %" PRIu64 "]",
              (uint64_t)patch_hit_loc, patch_covered ? "true" : "false", patch_hits);
    if (!patch_hits) {
        return;
    }
    if (!func_hits_len) {
        trace_log("[patch-func] [location 0x%" PRIx64 "] [entry 0] [hits %" PRIu64 "]",
                  (uint64_t)patch_hit_loc, patch_unknown_hits);
        return;
    }
    qsort(func_hits, func_hits_len, sizeof(*func_hits), cmp_func_hit);
    for (i = 0; i < func_hits_len; i++) {
        trace_log("[patch-func] [location 0x%" PRIx64 "] [entry 0x%" PRIx64 "] [hits %" PRIu64 "]",
                  (uint64_t)patch_hit_loc, (uint64_t)func_hits[i].entry,
                  func_hits[i].hits);
    }
}

static void print_file_summary(void)
{
    BinradarFd *fd;

    if (!patch_func_entry) {
        return;
    }
    trace_log("[file-trace] [summary] [location 0x%" PRIx64 "] [covered %s] [open hits %" PRIu64 "] [reads before patch %" PRIu64 "] [reads after patch %" PRIu64 "]",
              (uint64_t)patch_func_entry, patch_func_entry_covered ? "true" : "false",
              open_hits, reads_before_patch, reads_after_patch);
    for (fd = fds; fd; fd = fd->next) {
        if (fd->group) {
            trace_log("[file-trace] [fd %d] [offset %" PRId64 "] [seekable %s]",
                      fd->fd, fd->group->offset, fd->seekable ? "true" : "false");
        }
    }
}

static void print_bb_summary(void)
{
    size_t i;

    if (!trace_basic_blocks) {
        return;
    }
    qsort(basic_blocks, basic_blocks_len, sizeof(*basic_blocks), cmp_addr_hit);
    trace_log("[bb] [count %zu]", basic_blocks_len);
    for (i = 0; i < basic_blocks_len; i++) {
        trace_log("[bb] [idx %zu] [addr 0x%" PRIx64 "] [hits %" PRIu64 "]",
                  i, (uint64_t)basic_blocks[i].addr, basic_blocks[i].hits);
    }
}

static void print_final_common(void)
{
    flush_pending_patch();
    print_patch_summary();
    print_file_summary();
    print_bb_summary();
    fflush(stderr);
}

void binradar_trace_report_signal(void *cpu_env, int sig)
{
    CPUArchState *env = cpu_env;
    target_ulong pc;

    if (!trace_enabled || printed_final) {
        return;
    }
    printed_final = true;
    pc = PC_GET(env);
    trace_log("exit-raw Ok(Crash)");
    trace_log("[qemu-exit] [kind crash] [detail target crash]");
    trace_log("[exit] [result crash]");
    trace_log("[crash] [signal %d] [name %s]", target_to_host_signal(sig),
              target_signal_name(sig));
    print_stacktrace(pc);
    print_final_common();
}

void binradar_trace_report_exit(void *cpu_env, int code)
{
    (void)cpu_env;
    (void)code;

    if (!trace_enabled || printed_final) {
        return;
    }
    printed_final = true;
    trace_log("exit-raw Ok(End(GuestShutdown))");
    trace_log("[qemu-exit] [kind end] [detail guest requested shutdown]");
    trace_log("[exit] [result ok]");
    print_final_common();
}

void HELPER(binradar_trace_start)(target_ulong pc)
{
    binradar_trace_start(pc);
}

void HELPER(binradar_trace_bb)(target_ulong pc)
{
    binradar_trace_record_bb(pc);
}

void HELPER(binradar_trace_insn)(target_ulong pc)
{
    binradar_trace_insn_hit(pc);
}

void HELPER(binradar_trace_call)(target_ulong pc, target_ulong return_addr,
                                target_ulong entry)
{
    binradar_trace_call(pc, return_addr, entry);
}

void HELPER(binradar_trace_ret)(target_ulong pc, target_ulong return_addr)
{
    binradar_trace_ret(pc, return_addr);
}
