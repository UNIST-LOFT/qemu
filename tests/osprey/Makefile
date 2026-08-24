# OSPREY (in-process type inference) test harness.
#
# Verifies the Stage 1-5 pipeline end to end by running a small guest
# under the tracer with BINRADAR_OSPREY_ENABLE=1 in binradar forkserver
# mode and asserting on the structured `[osprey]` / `[inferred]` log
# rows emitted by the parent (closure, inference, decode, consumer).
#
# Usage:
#   make            # build guests + PLT files, run all tests
#   make check      # alias for `make`
#   make guests     # build guest binaries only
#   make plts       # generate PLT files only
#   make clean      # remove build products

QEMU      := ../../build/x86_64-linux-user/qemu-x86_64
SOLVER    := ../../../solver/build/solver-smt
RUNNER    := $(CURDIR)/run_test.py
GEN_PLT   := $(CURDIR)/../provenance/gen_plt.py
GUESTS    := $(CURDIR)/guests
WORK      := $(CURDIR)/work

CC        ?= gcc
CFLAGS    := -O0 -g -fno-pie -no-pie -fno-stack-protector -U_FORTIFY_SOURCE -fno-builtin
LDFLAGS   := -no-pie

TESTS := osprey_deref

GUEST_BINS := $(addprefix $(WORK)/,$(TESTS))
PLT_FILES  := $(addprefix $(WORK)/,$(addsuffix .plt,$(TESTS)))

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
	mkdir -p $@

clean:
	rm -rf $(WORK)
