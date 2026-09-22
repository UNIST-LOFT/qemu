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
               ../../build/x86_64-linux-user/linux-user/osprey-runtime.o \
               ../../build/x86_64-linux-user/linux-user/osprey-mutation.o \
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
BP_UNIT_BIN := $(WORK)/stage5_bp
BP_ASAN_BIN := $(WORK)/stage5_bp_asan
DECODE_UNIT_BIN := $(WORK)/stage6_decode
DECODE_ASAN_BIN := $(WORK)/stage6_decode_asan
OSPREY_SRCS := ../../linux-user/osprey.c \
               ../../linux-user/osprey-facts.c \
               ../../linux-user/osprey-graph.c \
               ../../linux-user/osprey-rules.c \
               ../../linux-user/osprey-infer.c \
               ../../linux-user/osprey-decode.c \
               ../../linux-user/osprey-relations.c \
               ../../linux-user/osprey-runtime.c \
               ../../linux-user/osprey-mutation.c \
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

TESTS := osprey_deref t01_regions t01_clone t02_chunk_widths t04_mpx t05_enter_fault t06_control_reject t07_legacy_width_reject t08_bound_reject t09_address_origins t10_value_origins t11_modeled_copies t12_allocator_facts t13_rule_graph t14_typed_mutation t15_huft_build t16_symbolic_boundary

GUEST_BINS := $(addprefix $(WORK)/,$(TESTS))
PLT_FILES  := $(addprefix $(WORK)/,$(addsuffix .plt,$(TESTS)))

.PHONY: check inventory run unit unit-asan unit-asan-osprey \
        unit-stage3-relations unit-stage3-relations-asan \
        unit-stage3-graph unit-stage3-graph-asan \
        unit-stage3-rules unit-stage3-rules-asan \
        unit-stage4-exact unit-stage4-exact-asan \
        unit-stage5-bp unit-stage5-bp-asan \
        unit-stage6-decode unit-stage6-decode-asan \
        unit-stage7-mutation unit-stage7-mutation-asan \
        unit-stage7-runtime unit-stage7-runtime-asan \
        unit-b1-mutation unit-b1-mutation-asan guests plts clean
check: inventory run unit unit-asan-osprey unit-stage3-relations \
       unit-stage3-relations-asan unit-stage3-graph unit-stage3-graph-asan \
       unit-stage3-rules unit-stage3-rules-asan unit-stage4-exact \
       unit-stage4-exact-asan unit-stage5-bp unit-stage5-bp-asan \
       unit-stage6-decode unit-stage6-decode-asan \
       unit-stage7-mutation unit-stage7-mutation-asan \
       unit-stage7-runtime unit-stage7-runtime-asan \
       unit-b1-mutation unit-b1-mutation-asan
run unit unit-asan-osprey unit-stage3-relations unit-stage3-relations-asan \
unit-stage3-graph unit-stage3-graph-asan unit-stage3-rules \
unit-stage3-rules-asan unit-stage4-exact unit-stage4-exact-asan \
unit-stage5-bp unit-stage5-bp-asan unit-stage6-decode \
unit-stage6-decode-asan unit-stage7-mutation \
unit-stage7-mutation-asan unit-stage7-runtime unit-stage7-runtime-asan \
unit-b1-mutation unit-b1-mutation-asan: inventory
inventory:
	@python3 $(INVENTORY)
run: guests plts
	@$(RUNNER) $(GUESTS) $(WORK) $(QEMU) --quiet
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

# t14_typed_mutation: Stage-7.5 applied-state fixture.  Keep the global
# cells and same-site heap targets in a PIE guest so observations can assert
# concrete child state without using host addresses as semantic identity.
$(WORK)/t14_typed_mutation: $(GUESTS)/t14_typed_mutation.c | $(WORK)
	$(CC) -O0 -g -fPIE -pie -fno-omit-frame-pointer -fno-stack-protector \
		-U_FORTIFY_SOURCE -fno-builtin -o $@ $<

# t15_huft_build: Stage-9 ranking fixture.  The debug twin and stripped PIE
# are produced from the same source and compiler flags; the tracer executes
# the stripped file while evaluation reads DWARF from the twin.
# t16_symbolic_boundary: Stage-7 symbolic boundary-advisor fixture.  Keep it
# PIE-free (fixed address) so the observed global cell and the branch are
# identical across runs, and keep the threshold constant visible in the
# instruction stream so the recorded comparison is the one under test.
$(WORK)/t16_symbolic_boundary: $(GUESTS)/t16_symbolic_boundary.c | $(WORK)
	$(CC) -O0 -g -fno-pie -no-pie -fno-omit-frame-pointer \
		-fno-stack-protector -U_FORTIFY_SOURCE -fno-builtin -o $@ $<

$(WORK)/t15_huft_build: $(GUESTS)/t15_huft_build.c | $(WORK)
	$(CC) -O0 -g -fPIE -pie -fomit-frame-pointer -fno-stack-protector \
		-U_FORTIFY_SOURCE -fno-builtin -o $@.debug $<
	cp $@.debug $@
	strip --strip-all $@

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

unit-stage5-bp: $(BP_UNIT_BIN)
	@$(BP_UNIT_BIN)

$(BP_UNIT_BIN): stage5_bp_test.c stage5_bp_reference.c \
		stage5_bp_reference.h stage3_test_support.c $(OSPREY_OBJS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -o $@ stage5_bp_test.c \
		stage5_bp_reference.c stage3_test_support.c $(OSPREY_OBJS) \
		-lglib-2.0 -lpthread -lm

unit-stage5-bp-asan: $(BP_ASAN_BIN)
	@ASAN_OPTIONS=detect_leaks=1 $(BP_ASAN_BIN)

$(BP_ASAN_BIN): stage5_bp_test.c stage5_bp_reference.c \
		stage5_bp_reference.h stage3_test_support.c $(OSPREY_ASAN_OBJS) | $(WORK)
	$(CC) $(ASAN_CFLAGS) -o $@ stage5_bp_test.c \
		stage5_bp_reference.c stage3_test_support.c $(OSPREY_ASAN_OBJS) \
		-lglib-2.0 -lpthread -lm

unit-stage6-decode: $(DECODE_UNIT_BIN)
	@$(DECODE_UNIT_BIN)

$(DECODE_UNIT_BIN): stage6_decode_test.c stage6_decode_reference.c \
		stage6_decode_reference.h stage3_test_support.c $(OSPREY_OBJS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -o $@ stage6_decode_test.c \
		stage6_decode_reference.c stage3_test_support.c $(OSPREY_OBJS) \
		-lglib-2.0 -lpthread -lm

unit-stage6-decode-asan: $(DECODE_ASAN_BIN)
	@ASAN_OPTIONS=detect_leaks=1 $(DECODE_ASAN_BIN)

$(DECODE_ASAN_BIN): stage6_decode_test.c stage6_decode_reference.c \
		stage6_decode_reference.h stage3_test_support.c $(OSPREY_ASAN_OBJS) | $(WORK)
	$(CC) $(ASAN_CFLAGS) -o $@ stage6_decode_test.c \
		stage6_decode_reference.c stage3_test_support.c $(OSPREY_ASAN_OBJS) \
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

# Stage 7.1 focused runner: compiles linux-user/snapshot.c into the test
# translation unit so the child-side record writers and the parent-side
# analyze_collected_data() are reachable (their state is static in
# snapshot.c).  snapshot.c provides log_msg/trace_mem/is_valid_address/
# mr_manager_heap_search_pub, so the shared stage3_test_support.c stubs
# for those are NOT linked here (duplicate strong definitions would
# break the link).  The OSPREY objects must be recompiled for ASan
# (OSPREY_ASAN_OBJS); snapshot.c is compiled by the test itself with
# the same sanitizer flags.
MUTATION_UNIT_BIN := $(WORK)/stage7_mutation
MUTATION_ASAN_BIN := $(WORK)/stage7_mutation_asan
SBSV_OBJS := $(addprefix $(WORK)/,sbsv.o sbsv_parser.o)
E9_RANGES_SRC := ../../linux-user/e9-ranges.c
E9_RANGES_HDR := ../../linux-user/e9-ranges.h
MUTATION_INCLUDED_SRCS := ../../linux-user/snapshot.c \
                          ../../linux-user/snapshot.h
MUTATION_CORE_SRC := ../../linux-user/snapshot-mutation.c
MUTATION_CORE_HDR := ../../linux-user/snapshot-mutation-internal.h
OBSERVATION_SRC := ../../linux-user/snapshot-observation.c
OBSERVATION_HDR := ../../linux-user/snapshot-observation.h
OSPREY_ADAPTER_SRC := ../../linux-user/snapshot-osprey-adapter.c
OSPREY_ADAPTER_HDR := ../../linux-user/snapshot-osprey-adapter.h
CACHE_SESSION_SRC := ../../linux-user/binradar-cache.c
CACHE_SESSION_HDR := ../../linux-user/binradar-cache.h
FORKSERVER_SRC := ../../linux-user/binradar-forkserver.c
FORKSERVER_HDR := ../../linux-user/binradar-forkserver.h
# The symbolic boundary advisor is compiled into the test translation unit
# (stage7_mutation_test.c includes snapshot-mutation-symbolic.c) so the focused
# runner can drive its static configuration and budgets directly.  It is still
# listed as a prerequisite so edits rebuild the runner.  The tracer build
# compiles the same source as a standalone object (linux-user/Makefile.objs).
MUTATION_ADVISOR_SRC := ../../linux-user/snapshot-mutation-symbolic.c
MUTATION_ADVISOR_HDRS := ../../linux-user/snapshot-mutation.h \
                         ../../linux-user/snapshot-mutation-symbolic.h

# GQueue frees links through GLib's slice allocator. Debug blocks makes an
# allocator-family mismatch fail at the first queue pop instead of corrupting
# the forkserver parent's heap after hundreds of mutation epochs.
unit-stage7-mutation: $(MUTATION_UNIT_BIN)
	@G_SLICE=debug-blocks $(MUTATION_UNIT_BIN)

$(MUTATION_UNIT_BIN): stage7_mutation_test.c stage7_mutation_reference.c \
		stage7_mutation_reference.h $(MUTATION_INCLUDED_SRCS) \
		$(MUTATION_CORE_SRC) $(MUTATION_CORE_HDR) \
		$(OBSERVATION_SRC) $(OBSERVATION_HDR) \
		$(OSPREY_ADAPTER_SRC) $(OSPREY_ADAPTER_HDR) \
		$(CACHE_SESSION_SRC) $(CACHE_SESSION_HDR) \
		$(FORKSERVER_SRC) $(FORKSERVER_HDR) \
		$(MUTATION_ADVISOR_SRC) $(MUTATION_ADVISOR_HDRS) \
		$(E9_RANGES_SRC) $(E9_RANGES_HDR) \
		$(OSPREY_OBJS) $(SBSV_OBJS) $(OSPREY_HEADERS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -o $@ stage7_mutation_test.c \
		stage7_mutation_reference.c $(MUTATION_CORE_SRC) \
		$(OBSERVATION_SRC) $(OSPREY_ADAPTER_SRC) $(CACHE_SESSION_SRC) \
		$(FORKSERVER_SRC) $(E9_RANGES_SRC) \
		$(OSPREY_OBJS) $(SBSV_OBJS) -lglib-2.0 -lpthread -lm

unit-stage7-mutation-asan: $(MUTATION_ASAN_BIN)
	@ASAN_OPTIONS=detect_leaks=1 $(MUTATION_ASAN_BIN)

# ASan variant: the test TU (including the included snapshot.c) is
# compiled with sanitizers, and the OSPREY objects are the dedicated
# ASan-compiled objects.  sbsv needs ASan-compiled copies too.
SBSV_ASAN_OBJS := $(addprefix $(WORK)/,sbsv.asan.o sbsv_parser.asan.o)

$(MUTATION_ASAN_BIN): stage7_mutation_test.c stage7_mutation_reference.c \
		stage7_mutation_reference.h $(MUTATION_INCLUDED_SRCS) \
		$(MUTATION_CORE_SRC) $(MUTATION_CORE_HDR) \
		$(OBSERVATION_SRC) $(OBSERVATION_HDR) \
		$(OSPREY_ADAPTER_SRC) $(OSPREY_ADAPTER_HDR) \
		$(CACHE_SESSION_SRC) $(CACHE_SESSION_HDR) \
		$(FORKSERVER_SRC) $(FORKSERVER_HDR) \
		$(MUTATION_ADVISOR_SRC) $(MUTATION_ADVISOR_HDRS) \
		$(E9_RANGES_SRC) $(E9_RANGES_HDR) \
		$(OSPREY_ASAN_OBJS) $(SBSV_ASAN_OBJS) $(OSPREY_HEADERS) | $(WORK)
	$(CC) $(ASAN_CFLAGS) -o $@ stage7_mutation_test.c \
		stage7_mutation_reference.c $(MUTATION_CORE_SRC) \
		$(OBSERVATION_SRC) $(OSPREY_ADAPTER_SRC) $(CACHE_SESSION_SRC) \
		$(FORKSERVER_SRC) $(E9_RANGES_SRC) \
		$(OSPREY_ASAN_OBJS) $(SBSV_ASAN_OBJS) -lglib-2.0 -lpthread -lm

$(WORK)/sbsv.asan.o: ../../linux-user/sbsv.c | $(WORK)
	$(CC) $(ASAN_CFLAGS) -c -o $@ $<

$(WORK)/sbsv_parser.asan.o: ../../linux-user/sbsv_parser.c | $(WORK)
	$(CC) $(ASAN_CFLAGS) -c -o $@ $<

# Plain sbsv objects for the non-ASan mutation unit (the test TU already
# carries the snapshot.c integration, so only the parsers are needed).
$(WORK)/sbsv.o: ../../linux-user/sbsv.c | $(WORK)
	$(CC) $(UNIT_CFLAGS) -c -o $@ $<

$(WORK)/sbsv_parser.o: ../../linux-user/sbsv_parser.c | $(WORK)
	$(CC) $(UNIT_CFLAGS) -c -o $@ $<

# Stage 7.2 focused runner: the production resolver uses a copied runtime
# index, while the test links an independent slow reference scanner.
RUNTIME_UNIT_BIN := $(WORK)/stage7_runtime
RUNTIME_ASAN_BIN := $(WORK)/stage7_runtime_asan

unit-stage7-runtime: $(RUNTIME_UNIT_BIN)
	@$(RUNTIME_UNIT_BIN)

$(RUNTIME_UNIT_BIN): stage7_runtime_test.c stage7_mutation_reference.c \
		stage7_mutation_reference.h stage3_test_support.c \
		$(OSPREY_OBJS) $(OSPREY_HEADERS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -o $@ stage7_runtime_test.c \
		stage7_mutation_reference.c stage3_test_support.c $(OSPREY_OBJS) \
		-lglib-2.0 -lpthread -lm

unit-stage7-runtime-asan: $(RUNTIME_ASAN_BIN)
	@ASAN_OPTIONS=detect_leaks=1 $(RUNTIME_ASAN_BIN)

$(RUNTIME_ASAN_BIN): stage7_runtime_test.c stage7_mutation_reference.c \
		stage7_mutation_reference.h stage3_test_support.c \
		$(OSPREY_ASAN_OBJS) $(OSPREY_HEADERS) | $(WORK)
	$(CC) $(ASAN_CFLAGS) -o $@ stage7_runtime_test.c \
		stage7_mutation_reference.c stage3_test_support.c \
		$(OSPREY_ASAN_OBJS) -lglib-2.0 -lpthread -lm

# B1 focused runner: facts-only compact model construction.  It links no
# snapshot.c/B0 coordinator; all facts are parent-owned test GArrays.
B1_UNIT_BIN := $(WORK)/b1_mutation
B1_ASAN_BIN := $(WORK)/b1_mutation_asan

unit-b1-mutation: $(B1_UNIT_BIN)
	@$(B1_UNIT_BIN)

$(B1_UNIT_BIN): b1_mutation_test.c stage3_test_support.c \
		$(OSPREY_OBJS) $(OSPREY_HEADERS) | $(WORK)
	$(CC) $(UNIT_CFLAGS) -o $@ b1_mutation_test.c \
		stage3_test_support.c $(OSPREY_OBJS) -lglib-2.0 -lpthread -lm

unit-b1-mutation-asan: $(B1_ASAN_BIN)
	@ASAN_OPTIONS=detect_leaks=1 $(B1_ASAN_BIN)

$(B1_ASAN_BIN): b1_mutation_test.c stage3_test_support.c \
		$(OSPREY_ASAN_OBJS) $(OSPREY_HEADERS) | $(WORK)
	$(CC) $(ASAN_CFLAGS) -o $@ b1_mutation_test.c \
		stage3_test_support.c $(OSPREY_ASAN_OBJS) -lglib-2.0 -lpthread -lm
