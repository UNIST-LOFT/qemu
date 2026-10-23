/* Function-boundary evidence for BinRadar tail transfers.  No guest reads. */
#include "qemu/osdep.h"
#include "qemu.h"
#include "qemu/bswap.h"
#include "qemuafl/binradar-trace.h"
#include "elf.h"

typedef struct TraceElf {
    const uint8_t *data;
    size_t size;
    uint64_t phoff;
    unsigned phnum, phsize, word;
} TraceElf;

typedef struct TraceCursor {
    const uint8_t *p, *end;
    uint64_t address;
    unsigned word;
    bool ok;
} TraceCursor;

static uint64_t take(TraceCursor *c, unsigned n)
{
    uint64_t v = 0;
    unsigned i;
    if (!c->ok || n > 8 || n > c->end - c->p) {
        c->ok = false;
        return 0;
    }
    for (i = 0; i < n; i++) {
        v |= (uint64_t)*c->p++ << (i * 8);
    }
    c->address += n;
    return v;
}

static uint64_t leb(TraceCursor *c, bool sign)
{
    uint64_t v = 0, b;
    unsigned shift = 0;
    do {
        b = take(c, 1);
        if (!c->ok || shift >= 64 || (shift == 63 && (b & 0x7e) &&
                                     (!sign || (b & 0x7f) != 0x7f))) {
            c->ok = false;
            return 0;
        }
        v |= (b & 0x7f) << shift;
        shift += 7;
    } while (b & 0x80);
    if (sign && shift < 64 && (b & 0x40)) {
        v |= UINT64_MAX << shift;
    }
    return v;
}

static uint64_t encoded(TraceCursor *c, unsigned enc, uint64_t data_base)
{
    uint64_t base = c->address, v;
    unsigned n;
    /* Indirect, aligned, textrel and funcrel require evidence we do not have. */
    if ((enc & 0x80) || ((enc & 0x70) != 0 &&
        (enc & 0x70) != 0x10 && (enc & 0x70) != 0x30)) {
        c->ok = false;
        return 0;
    }
    switch (enc & 0x0f) {
    case 0: v = take(c, c->word); break;
    case 1: v = leb(c, false); break;
    case 9: v = leb(c, true); break;
    case 2: case 3: case 4:
    case 10: case 11: case 12:
        n = 1U << ((enc & 7) - 1);
        v = take(c, n);
        if ((enc & 8) && n < 8) {
            v = (uint64_t)((int64_t)(v << (64 - n * 8)) >> (64 - n * 8));
        }
        break;
    default: c->ok = false; return 0;
    }
    if ((enc & 0x70) == 0x10) {
        v += base;
    } else if ((enc & 0x70) == 0x30) {
        v += data_base;
    }
    return v;
}

static uint64_t field(const uint8_t *p, unsigned n)
{
    return n == 8 ? ldq_le_p(p) : ldl_le_p(p);
}

static const uint8_t *phdr(const TraceElf *e, unsigned i)
{
    return e->data + e->phoff + (uint64_t)i * e->phsize;
}

static bool virtual_cursor(const TraceElf *e, uint64_t addr, TraceCursor *c)
{
    unsigned i;
    for (i = 0; i < e->phnum; i++) {
        const uint8_t *p = phdr(e, i);
        uint64_t off = field(p + (e->word == 8 ? 8 : 4), e->word);
        uint64_t va = field(p + (e->word == 8 ? 16 : 8), e->word);
        uint64_t len = field(p + (e->word == 8 ? 32 : 16), e->word);
        if (ldl_le_p(p) == PT_LOAD && addr >= va && addr - va < len &&
            off <= e->size && len <= e->size - off) {
            *c = (TraceCursor){ e->data + off + (addr - va),
                               e->data + off + len, addr, e->word, true };
            return true;
        }
    }
    return false;
}

static void load_fde(const TraceElf *e, uint64_t address, uint64_t expected,
                     target_ulong bias)
{
    TraceCursor f, c, aug;
    uint64_t length, cie_address, aug_size, entry, size;
    const uint8_t *augmentation, *a;
    unsigned version, encoding = 0;
    bool z;

    if (!virtual_cursor(e, address, &f)) {
        return;
    }
    length = take(&f, 4);
    if (!f.ok || length < 8 || length == UINT32_MAX || length > f.end - f.p) {
        return;
    }
    f.end = f.p + length;
    cie_address = f.address;
    cie_address -= take(&f, 4);
    if (!virtual_cursor(e, cie_address, &c)) {
        return;
    }
    length = take(&c, 4);
    if (!c.ok || length < 5 || length == UINT32_MAX || length > c.end - c.p) {
        return;
    }
    c.end = c.p + length;
    if (take(&c, 4) != 0) {
        return;
    }
    version = take(&c, 1);
    if (version != 1 && version != 3 && version != 4) {
        return;
    }
    augmentation = c.p;
    while (c.ok && take(&c, 1)) {
        /* Bounded by this CIE, including malformed unterminated strings. */
    }
    if (!c.ok) {
        return;
    }
    if (version == 4 && (take(&c, 1) != e->word || take(&c, 1) != 0)) {
        return;
    }
    leb(&c, false); /* code alignment */
    leb(&c, true);  /* data alignment */
    if (version == 1) {
        take(&c, 1);
    } else {
        leb(&c, false);
    }
    z = *augmentation == 'z';
    if (z) {
        aug_size = leb(&c, false);
        if (!c.ok || aug_size > c.end - c.p) {
            return;
        }
        aug = c;
        aug.end = aug.p + aug_size;
        for (a = augmentation + 1; *a && aug.ok; a++) {
            switch (*a) {
            case 'L': take(&aug, 1); break;
            case 'R': encoding = take(&aug, 1); break;
            case 'P': {
                unsigned enc = take(&aug, 1);
                /* Personality may be indirect; only consume its encoding. */
                encoded(&aug, enc & ~0x80, 0);
                break;
            }
            case 'S': break;
            default: aug.ok = false; break;
            }
        }
        if (!aug.ok) {
            return;
        }
    } else if (*augmentation) {
        return;
    }
    if (!c.ok) {
        return;
    }
    entry = encoded(&f, encoding, 0);
    size = encoded(&f, encoding & 0x0f, 0);
    if (f.ok && entry == expected && size && entry + size > entry &&
        entry + bias >= entry && entry + bias + size > entry + bias) {
        binradar_trace_add_unwind_function(entry + bias, size);
    }
}

void binradar_trace_load_elf(int fd, target_ulong bias)
{
    GMappedFile *map;
    TraceElf e = { 0 };
    unsigned i;

    if (!binradar_trace_is_enabled()) {
        return;
    }
    map = g_mapped_file_new_from_fd(fd, false, NULL);
    if (!map) {
        return;
    }
    e.data = (const uint8_t *)g_mapped_file_get_contents(map);
    e.size = g_mapped_file_get_length(map);
    if (e.size < 64 || memcmp(e.data, ELFMAG, SELFMAG) ||
        e.data[EI_DATA] != ELFDATA2LSB ||
        (e.data[EI_CLASS] != ELFCLASS32 && e.data[EI_CLASS] != ELFCLASS64)) {
        goto out;
    }
    e.word = e.data[EI_CLASS] == ELFCLASS64 ? 8 : 4;
    e.phoff = field(e.data + (e.word == 8 ? 32 : 28), e.word);
    e.phsize = lduw_le_p(e.data + (e.word == 8 ? 54 : 42));
    e.phnum = lduw_le_p(e.data + (e.word == 8 ? 56 : 44));
    if (e.phsize < (e.word == 8 ? 56 : 32) || e.phoff > e.size ||
        e.phnum > (e.size - e.phoff) / e.phsize) {
        goto out;
    }
    for (i = 0; i < e.phnum; i++) {
        const uint8_t *p = phdr(&e, i);
        uint64_t va, len, off, count, j;
        unsigned ptr_enc, count_enc, table_enc;
        TraceCursor c;
        if (ldl_le_p(p) != PT_GNU_EH_FRAME) {
            continue;
        }
        va = field(p + (e.word == 8 ? 16 : 8), e.word);
        off = field(p + (e.word == 8 ? 8 : 4), e.word);
        len = field(p + (e.word == 8 ? 32 : 16), e.word);
        if (off > e.size || len > e.size - off || len < 4) {
            continue;
        }
        c = (TraceCursor){ e.data + off, e.data + off + len, va, e.word, true };
        if (take(&c, 1) != 1) {
            continue;
        }
        ptr_enc = take(&c, 1);
        count_enc = take(&c, 1);
        table_enc = take(&c, 1);
        encoded(&c, ptr_enc, va);
        count = encoded(&c, count_enc, va);
        /* Each table record needs at least two bytes, even with LEB128. */
        if (!c.ok || count > (c.end - c.p) / 2) {
            continue;
        }
        for (j = 0; j < count && c.ok; j++) {
            uint64_t entry = encoded(&c, table_enc, va);
            uint64_t fde = encoded(&c, table_enc, va);
            if (c.ok) {
                load_fde(&e, fde, entry, bias);
            }
        }
    }
out:
    g_mapped_file_unref(map);
}
