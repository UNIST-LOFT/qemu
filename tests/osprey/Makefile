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
               ../../build/x86_64-linux-user/linux-user/osprey-decode.o \
               ../../build/x86_64-linux-user/linux-user/provenance.o \
               ../../build/x86_64-linux-user/linux-user/sem-events.o
UNIT_BIN   := $(WORK)/osprey_unit
UNIT_ASAN_BIN := $(WORK)/osprey_unit_asan
OSPREY_SRCS := ../../linux-user/osprey.c \
               ../../linux-user/osprey-facts.c \
               ../../linux-user/osprey-rules.c \
               ../../linux-user/osprey-infer.c \
               ../../linux-user/osprey-decode.c \
               ../../linux-user/provenance.c \
               ../../linux-user/sem-events.c
OSPREY_HEADERS := ../../linux-user/osprey.h \
                  ../../linux-user/osprey-internal.h \
                  ../../linux-user/provenance.h \
                  ../../linux-user/sem-events.h
OSPREY_ASAN_OBJS := $(addprefix $(WORK)/,$(notdir $(OSPREY_SRCS:.c=.asan.o)))
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
ASAN_CFLAGS := $(UNIT_CFLAGS) -fsanitize=address,undefined \
                -fno-omit-frame-pointer

CC        ?= gcc
CFLAGS    := -O0 -g -fno-pie -no-pie -fno-stack-protector -U_FORTIFY_SOURCE -fno-builtin
LDFLAGS   := -no-pie

TESTS := osprey_deref t01_regions t01_clone t02_chunk_widths

GUEST_BINS := $(addprefix $(WORK)/,$(TESTS))
PLT_FILES  := $(addprefix $(WORK)/,$(addsuffix .plt,$(TESTS)))

.PHONY: check run unit unit-asan unit-asan-osprey guests plts clean
check: run unit unit-asan-osprey
run: guests plts
	@$(RUNNER) $(GUESTS) $(WORK) $(QEMU) $(SOLVER) --quiet
unit: $(UNIT_BIN)
	@$(UNIT_BIN)
unit-asan: $(UNIT_ASAN_BIN)
	@ASAN_OPTIONS=detect_leaks=1 $(UNIT_ASAN_BIN)
unit-asan-osprey: $(WORK)/osprey_unit_asan_osprey
	@ASAN_OPTIONS=detect_leaks=1 $(WORK)/osprey_unit_asan_osprey
guests: $(GUEST_BINS)
plts: $(PLT_FILES)

$(WORK)/%: $(GUESTS)/%.c | $(WORK)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $<

# Stage-1 ASLR gate: canonical facts from two independent PIE runs must
# be byte-identical even though raw stack/heap/image addresses differ.
$(WORK)/t01_regions: $(GUESTS)/t01_regions.c | $(WORK)
	$(CC) -O0 -g -fPIE -pie -fno-stack-protector \
		-U_FORTIFY_SOURCE -fno-builtin -o $@ $<

$(WORK)/t01_clone: $(GUESTS)/t01_clone.c | $(WORK)
	$(CC) $(CFLAGS) $(LDFLAGS) -pthread -o $@ $<

# t02_chunk_widths: F01 width fixture — must be PIE so the dump_compare
# harness can verify byte-identity across load biases.
$(WORK)/t02_chunk_widths: $(GUESTS)/t02_chunk_widths.c | $(WORK)
	$(CC) -O0 -g -fPIE -pie -fno-stack-protector \
		-U_FORTIFY_SOURCE -fno-builtin -o $@ $<

$(WORK)/%.plt: $(WORK)/% $(GEN_PLT)
	python3 $(GEN_PLT) -o $@ $<

$(UNIT_BIN): unit_test.c $(OSPREY_OBJS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -o $@ unit_test.c $(OSPREY_OBJS) \
		-lglib-2.0 -lpthread -lm

$(UNIT_ASAN_BIN): unit_test.c $(OSPREY_OBJS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -fsanitize=address -fno-omit-frame-pointer \
		-o $@ unit_test.c $(OSPREY_OBJS) -lglib-2.0 -lpthread -lm

# Item 8: the OSPREY translation units themselves are compiled with
# ASan+UBSan and linked into a dedicated runner, so sanitizer coverage
# includes the ownership/lifecycle code, not just the stub harness.
$(WORK)/osprey_unit_asan_osprey: unit_test.c $(OSPREY_ASAN_OBJS) | $(WORK)
	$(CC) $(ASAN_CFLAGS) -o $@ unit_test.c $(OSPREY_ASAN_OBJS) \
		-lglib-2.0 -lpthread -lm

$(WORK)/%.asan.o: ../../linux-user/%.c $(OSPREY_HEADERS) | $(WORK)
	$(CC) $(ASAN_CFLAGS) -c -o $@ $<

$(WORK):
	mkdir -p $@

clean:
	rm -rf $(WORK)
