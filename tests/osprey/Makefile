# OSPREY (in-process type inference) test harness.
#
# Stage 0 validates fail-closed transaction ownership with a C unit runner
# and forkserver cases that reject known-invalid graphs/limits, retain the
# generic mutation queue, and reach iteration 2 without typed output.
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

# Stage-0 unit test: links the OSPREY translation units from the tracer
# build against a stub environment (see unit_test.c).
OSPREY_OBJS := ../../build/x86_64-linux-user/linux-user/osprey.o \
               ../../build/x86_64-linux-user/linux-user/osprey-facts.o \
               ../../build/x86_64-linux-user/linux-user/osprey-rules.o \
               ../../build/x86_64-linux-user/linux-user/osprey-infer.o \
               ../../build/x86_64-linux-user/linux-user/osprey-decode.o
UNIT_BIN   := $(WORK)/osprey_unit
UNIT_ASAN_BIN := $(WORK)/osprey_unit_asan
UNIT_CFLAGS := -iquote ../../build/linux-user -iquote ../../tcg \
               -iquote ../../tcg/i386 -iquote ../../ \
               -iquote ../../accel/tcg -iquote ../../include \
               -iquote ../../target/i386 -I../../linux-headers \
               -I../../build/linux-headers -I../../linux-user/x86_64 \
               -I../../linux-user/host/x86_64 -I../../linux-user \
               -iquote ../../build -iquote ../../build/x86_64-linux-user \
               -pthread -I/usr/include/glib-2.0 \
               -I/usr/lib/x86_64-linux-gnu/glib-2.0/include \
               -std=gnu99 -Wall -Werror -g -O0 -DNEED_CPU_H \
               -D_GNU_SOURCE -D_FILE_OFFSET_BITS=64

CC        ?= gcc
CFLAGS    := -O0 -g -fno-pie -no-pie -fno-stack-protector -U_FORTIFY_SOURCE -fno-builtin
LDFLAGS   := -no-pie

TESTS := osprey_deref

GUEST_BINS := $(addprefix $(WORK)/,$(TESTS))
PLT_FILES  := $(addprefix $(WORK)/,$(addsuffix .plt,$(TESTS)))

.PHONY: check run unit unit-asan guests plts clean
check: run unit
run: guests plts
	@$(RUNNER) $(GUESTS) $(WORK) $(QEMU) $(SOLVER) --quiet
unit: $(UNIT_BIN)
	@$(UNIT_BIN)
unit-asan: $(UNIT_ASAN_BIN)
	@ASAN_OPTIONS=detect_leaks=1 $(UNIT_ASAN_BIN)
guests: $(GUEST_BINS)
plts: $(PLT_FILES)

$(WORK)/%: $(GUESTS)/%.c | $(WORK)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $<

$(WORK)/%.plt: $(WORK)/% $(GEN_PLT)
	python3 $(GEN_PLT) -o $@ $<

$(UNIT_BIN): unit_test.c $(OSPREY_OBJS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -o $@ unit_test.c $(OSPREY_OBJS) \
		-lglib-2.0 -lpthread -lm

$(UNIT_ASAN_BIN): unit_test.c $(OSPREY_OBJS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -fsanitize=address -fno-omit-frame-pointer \
		-o $@ unit_test.c $(OSPREY_OBJS) -lglib-2.0 -lpthread -lm

$(WORK):
	mkdir -p $@

clean:
	rm -rf $(WORK)
