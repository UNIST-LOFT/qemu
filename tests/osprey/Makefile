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
INVENTORY := $(CURDIR)/check_semantic_inventory.py
GEN_PLT   := $(CURDIR)/../provenance/gen_plt.py
GUESTS    := $(CURDIR)/guests
WORK      := $(CURDIR)/work

# Stage-0 unit test: links the OSPREY translation units from the tracer
# build against a stub environment (see unit_test.c).
OSPREY_OBJS := ../../build/x86_64-linux-user/linux-user/osprey.o \
               ../../build/x86_64-linux-user/linux-user/osprey-facts.o \
               ../../build/x86_64-linux-user/linux-user/osprey-graph.o \
               ../../build/x86_64-linux-user/linux-user/osprey-rules.o \
               ../../build/x86_64-linux-user/linux-user/osprey-infer.o \
               ../../build/x86_64-linux-user/linux-user/osprey-decode.o \
               ../../build/x86_64-linux-user/linux-user/osprey-relations.o \
               ../../build/x86_64-linux-user/linux-user/provenance.o \
               ../../build/x86_64-linux-user/linux-user/sem-events.o
UNIT_BIN   := $(WORK)/osprey_unit
UNIT_ASAN_BIN := $(WORK)/osprey_unit_asan
REL_UNIT_BIN := $(WORK)/stage3_relations
REL_ASAN_BIN := $(WORK)/stage3_relations_asan
GRAPH_UNIT_BIN := $(WORK)/stage3_graph
GRAPH_ASAN_BIN := $(WORK)/stage3_graph_asan
RULES_UNIT_BIN := $(WORK)/stage3_rules
RULES_ASAN_BIN := $(WORK)/stage3_rules_asan
EXACT_UNIT_BIN := $(WORK)/stage4_exact
EXACT_ASAN_BIN := $(WORK)/stage4_exact_asan
OSPREY_SRCS := ../../linux-user/osprey.c \
               ../../linux-user/osprey-facts.c \
               ../../linux-user/osprey-graph.c \
               ../../linux-user/osprey-rules.c \
               ../../linux-user/osprey-infer.c \
               ../../linux-user/osprey-decode.c \
               ../../linux-user/osprey-relations.c \
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

TESTS := osprey_deref t01_regions t01_clone t02_chunk_widths t04_mpx t05_enter_fault t06_control_reject t07_legacy_width_reject t08_bound_reject t09_address_origins t10_value_origins t11_modeled_copies t12_allocator_facts t13_rule_graph

GUEST_BINS := $(addprefix $(WORK)/,$(TESTS))
PLT_FILES  := $(addprefix $(WORK)/,$(addsuffix .plt,$(TESTS)))

.PHONY: check inventory run unit unit-asan unit-asan-osprey \
        unit-stage3-relations unit-stage3-relations-asan \
        unit-stage3-graph unit-stage3-graph-asan \
        unit-stage3-rules unit-stage3-rules-asan \
        unit-stage4-exact unit-stage4-exact-asan guests plts clean
check: inventory run unit unit-asan-osprey unit-stage3-relations \
       unit-stage3-relations-asan unit-stage3-graph unit-stage3-graph-asan \
       unit-stage3-rules unit-stage3-rules-asan unit-stage4-exact \
       unit-stage4-exact-asan
run unit unit-asan-osprey unit-stage3-relations unit-stage3-relations-asan \
unit-stage3-graph unit-stage3-graph-asan unit-stage3-rules \
unit-stage3-rules-asan unit-stage4-exact unit-stage4-exact-asan: inventory
inventory:
	@python3 $(INVENTORY)
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

# Canonical F01-F06 ASLR gate: facts from independent PIE runs must be
# byte-identical even though raw stack/heap/image addresses differ.
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

$(WORK)/t04_mpx: $(GUESTS)/t04_mpx.c | $(WORK)
	$(CC) -O0 -g -fPIE -pie -fno-stack-protector \
		-U_FORTIFY_SOURCE -fno-builtin -o $@ $<

$(WORK)/t05_enter_fault: $(GUESTS)/t05_enter_fault.c | $(WORK)
	$(CC) -O0 -g -fPIE -pie -fno-stack-protector \
		-U_FORTIFY_SOURCE -fno-builtin -o $@ $<

# t09_address_origins: Stage-2.3 address-origin/F02 fixture — must be
# PIE so the dump_compare harness can verify byte-identity across load
# biases and resolve labeled producer/access symbols.
$(WORK)/t09_address_origins: $(GUESTS)/t09_address_origins.c | $(WORK)
	$(CC) -O0 -g -fPIE -pie -fno-omit-frame-pointer -fno-stack-protector \
		-U_FORTIFY_SOURCE -fno-builtin -o $@ $<

# t10_value_origins / t11_modeled_copies: Stage-2.4 VALUE/F03/F04 and
# modeled-copy fixtures — must be PIE so the dump_compare harness can
# verify byte-identity across load biases and resolve labeled symbols.
$(WORK)/t10_value_origins: $(GUESTS)/t10_value_origins.c | $(WORK)
	$(CC) -O0 -g -fPIE -pie -fno-omit-frame-pointer -fno-stack-protector \
		-U_FORTIFY_SOURCE -fno-builtin -o $@ $<

$(WORK)/t11_modeled_copies: $(GUESTS)/t11_modeled_copies.c | $(WORK)
	$(CC) -O0 -g -fPIE -pie -fno-omit-frame-pointer -fno-stack-protector \
		-U_FORTIFY_SOURCE -fno-builtin -o $@ $<

# t12_allocator_facts: exact Stage-2.5 malloc/calloc/realloc matrix.
$(WORK)/t12_allocator_facts: $(GUESTS)/t12_allocator_facts.c | $(WORK)
	$(CC) -O0 -g -fPIE -pie -fno-omit-frame-pointer -fno-stack-protector \
		-U_FORTIFY_SOURCE -fno-builtin -o $@ $<

# t13_rule_graph: complete Stage-3 relation/graph integration fixture.
$(WORK)/t13_rule_graph: $(GUESTS)/t13_rule_graph.c | $(WORK)
	$(CC) -O0 -g -fPIE -pie -fno-omit-frame-pointer -fno-stack-protector \
		-U_FORTIFY_SOURCE -fno-builtin -o $@ $<

$(WORK)/%.plt: $(WORK)/% $(GEN_PLT)
	python3 $(GEN_PLT) -o $@ $<

$(UNIT_BIN): unit_test.c $(OSPREY_OBJS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -o $@ unit_test.c $(OSPREY_OBJS) \
		-lglib-2.0 -lpthread -lm

unit-stage3-relations: $(REL_UNIT_BIN)
	@$(REL_UNIT_BIN)

$(REL_UNIT_BIN): stage3_relations_test.c stage3_reference.c \
		stage3_test_support.c $(OSPREY_OBJS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -o $@ stage3_relations_test.c \
		stage3_reference.c stage3_test_support.c $(OSPREY_OBJS) \
		-lglib-2.0 -lpthread -lm

unit-stage3-relations-asan: $(REL_ASAN_BIN)
	@ASAN_OPTIONS=detect_leaks=1 $(REL_ASAN_BIN)

$(REL_ASAN_BIN): stage3_relations_test.c stage3_reference.c \
		stage3_test_support.c $(OSPREY_ASAN_OBJS) | $(WORK)
	$(CC) $(ASAN_CFLAGS) -o $@ stage3_relations_test.c \
		stage3_reference.c stage3_test_support.c $(OSPREY_ASAN_OBJS) \
		-lglib-2.0 -lpthread -lm

unit-stage3-graph: $(GRAPH_UNIT_BIN)
	@$(GRAPH_UNIT_BIN)

$(GRAPH_UNIT_BIN): stage3_graph_test.c stage3_test_support.c \
		$(OSPREY_OBJS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -o $@ stage3_graph_test.c \
		stage3_test_support.c $(OSPREY_OBJS) -lglib-2.0 -lpthread -lm

unit-stage3-graph-asan: $(GRAPH_ASAN_BIN)
	@ASAN_OPTIONS=detect_leaks=1 $(GRAPH_ASAN_BIN)

$(GRAPH_ASAN_BIN): stage3_graph_test.c stage3_test_support.c \
		$(OSPREY_ASAN_OBJS) | $(WORK)
	$(CC) $(ASAN_CFLAGS) -o $@ stage3_graph_test.c \
		stage3_test_support.c $(OSPREY_ASAN_OBJS) -lglib-2.0 -lpthread -lm

unit-stage3-rules: $(RULES_UNIT_BIN)
	@$(RULES_UNIT_BIN)

$(RULES_UNIT_BIN): stage3_rules_test.c stage3_test_support.c \
		$(OSPREY_OBJS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -o $@ stage3_rules_test.c \
		stage3_test_support.c $(OSPREY_OBJS) \
		-lglib-2.0 -lpthread -lm

unit-stage3-rules-asan: $(RULES_ASAN_BIN)
	@ASAN_OPTIONS=detect_leaks=1 $(RULES_ASAN_BIN)

$(RULES_ASAN_BIN): stage3_rules_test.c stage3_test_support.c \
		$(OSPREY_ASAN_OBJS) | $(WORK)
	$(CC) $(ASAN_CFLAGS) -o $@ stage3_rules_test.c \
		stage3_test_support.c $(OSPREY_ASAN_OBJS) \
		-lglib-2.0 -lpthread -lm

unit-stage4-exact: $(EXACT_UNIT_BIN)
	@$(EXACT_UNIT_BIN)

$(EXACT_UNIT_BIN): stage4_exact_test.c stage4_exact_reference.c \
		stage4_exact_reference.h stage3_test_support.c $(OSPREY_OBJS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -o $@ stage4_exact_test.c \
		stage4_exact_reference.c stage3_test_support.c $(OSPREY_OBJS) \
		-lglib-2.0 -lpthread -lm

unit-stage4-exact-asan: $(EXACT_ASAN_BIN)
	@ASAN_OPTIONS=detect_leaks=1 $(EXACT_ASAN_BIN)

$(EXACT_ASAN_BIN): stage4_exact_test.c stage4_exact_reference.c \
		stage4_exact_reference.h stage3_test_support.c $(OSPREY_ASAN_OBJS) | $(WORK)
	$(CC) $(ASAN_CFLAGS) -o $@ stage4_exact_test.c \
		stage4_exact_reference.c stage3_test_support.c $(OSPREY_ASAN_OBJS) \
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
