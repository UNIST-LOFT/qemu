# Provenance (pointer-analysis / memcheck) test harness.
#
# Verifies the tracer's memory-error detection end to end by running small
# guests under qemu-x86_64 with BINRADAR_MEMCHECK_ENABLE=1 and asserting on
# the structured `[prov]` log lines emitted by the provenance engine.
#
# Usage:
#   make            # build guests + PLT files, run all tests
#   make check      # alias for `make`
#   make run        # build guests + PLT files, run all tests
#   make guests     # build guest binaries only
#   make plts       # generate PLT files only
#   make clean      # remove build products

QEMU      := ../../build/x86_64-linux-user/qemu-x86_64
SOLVER    := ../../../solver/build/solver-smt
RUNNER    := $(CURDIR)/run_test.py
GEN_PLT   := $(CURDIR)/gen_plt.py
GUESTS    := $(CURDIR)/guests
WORK      := $(CURDIR)/work

CC        ?= gcc
CFLAGS    := -O0 -g -fno-pie -no-pie -fno-stack-protector -U_FORTIFY_SOURCE -fno-builtin
LDFLAGS   := -no-pie

TESTS := t01_double_free t02_small_double_free t03_uaf_stack t04_uaf_heap \
         t05_off_oob t06_neg_off_oob t07_size_ext_oob t08_alloc_zero \
         t09_calloc_overflow t10_realloc_two_phase t11_realloc_shrink \
         t12_memcpy_model_oob t13_memset_model_oob t14_ea_static \
         t15_ea_dynamic t16_ea_forkserver t17_free_null t18_memchr_unaligned \
         t19_plt_child_trace t20_concolic_heap_off t21_crash_precedence \
         t22_region_halfopen t23_stack_region t24_heap_uninit_read \
         t25_global_uninit_read t26_use_after_free_gen t27_timeout_crash

GUEST_BINS := $(addprefix $(WORK)/,$(TESTS))
PLT_FILES  := $(addprefix $(WORK)/,$(addsuffix .plt,$(TESTS)))

# The test suite depends on the tracer and the solver binaries.
.PHONY: check run guests plts clean
check: run
run: guests plts
	@$(RUNNER) $(GUESTS) $(WORK) $(QEMU) $(SOLVER) --quiet
guests: $(GUEST_BINS)
plts: $(PLT_FILES)

$(WORK)/%: $(GUESTS)/%.c | $(WORK)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $<

$(WORK)/%.plt: $(WORK)/% $(GEN_PLT)
	python3 $(GEN_PLT) -o $@ $<

$(WORK):
	mkdir -p $(WORK)

clean:
	rm -rf $(WORK)
