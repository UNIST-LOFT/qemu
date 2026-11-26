/* Core-only OSPREY/provenance unit runners do not link QEMU's TCG engine.
 * Model the explicitly disabled observation boundary, and reject activation.
 * The real collector is exercised by tests/test_observation_native.py and
 * tests/test_observation_cli.py, never by these linker substitutes. */
#include "qemu/osdep.h"
#include "observation-analysis.h"

bool observation_analysis_enabled;

static void require_disabled(void)
{
    g_assert(!observation_analysis_enabled);
}

void observation_analysis_init(void)
{
    const char *mode = getenv("BINRADAR_OBS_ANALYSIS");
    g_assert(!mode || !strcmp(mode, "0"));
    require_disabled();
}

void observation_analysis_alloc(target_ulong base, target_ulong size,
                                target_ulong pc, uint64_t id, uint32_t gen,
                                int producer)
{
    (void)base; (void)size; (void)pc; (void)id; (void)gen; (void)producer;
    require_disabled();
}

void observation_analysis_free(target_ulong base)
{
    (void)base;
    require_disabled();
}

void observation_analysis_clobber(void)
{
    require_disabled();
}

void observation_analysis_overwrite(CPUArchState *env, target_ulong addr,
                                    target_ulong size, int cls)
{
    (void)env; (void)addr; (void)size; (void)cls;
    require_disabled();
}

void observation_analysis_copy(CPUArchState *env, target_ulong src,
                               target_ulong dst, target_ulong size)
{
    (void)env; (void)src; (void)dst; (void)size;
    require_disabled();
}

void observation_analysis_store(target_ulong addr, target_ulong size)
{
    (void)addr; (void)size;
    require_disabled();
}

void observation_analysis_unsupported(const char *reason)
{
    (void)reason;
    require_disabled();
}

void observation_analysis_finding(void)
{
    require_disabled();
}
