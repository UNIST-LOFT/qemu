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
CFLAGS   := -O0 -g -fno-pie -no-pie -fno-stack-protector -U_FORTIFY_SOURCE -fno-builtin
LDFLAGS  := -no-pie

TESTS := t01_double_free t02_small_double_free t03_uaf_stack t04_uaf_heap \
         t05_off_oob t06_neg_off_oob t07_size_ext_oob t08_alloc_zero \
         t09_calloc_overflow t10_realloc_two_phase t11_realloc_shrink \
         t12_memcpy_model_oob t13_memset_model_oob t14_ea_static \
         t15_ea_dynamic t16_ea_forkserver t17_free_null t18_memchr_unaligned \
         t19_plt_child_trace t20_concolic_heap_off t21_crash_precedence \
         t22_region_halfopen t23_stack_region t24_heap_uninit_read \
         t25_global_uninit_read t26_use_after_free_gen t27_timeout_crash \
         t28_unknown_no_uaf t29_push_pop_uaf t30_untagged_pop_unknown \
         t31_int_overwrite_clears t32_highbyte_clears t33_xchg_swap \
         t34_failed_malloc t35_same_addr_realloc t36_self_overwrite_load \
         t37_atomic_rmw t38_x87_store_semantics t39_failed_access_ordering \
         t39b_failed_access_success t42_mapping_reuse t43_syscall_output \
         t44_simd_overlap t45_post_finding_query t46_ea_tagged_promotion \
         t47_ea_index_scale t47_ea_seg_override t47_ea_addr32 \
         t47_ea_negative_disp t48_sticky_first_finding \
         t49_sticky_unknown_fallback t50_strcpy_model_oob \
         t51_strncpy_model_padding_oob t52_strcpy_fault_ordering \
         t53_memcpy_fault_ordering t54_zero_length_models \
         t55_strcmp_exact_ranges t56_memmove_overlap_symbolic \
         t57_syscall_failed_stat_tag_intact t58_stat_adjacent_untouched \
         t59_partial_readv_exact t60_zero_len_recvfrom_metadata \
         t61_recvfrom_addr_addrlen t62_recvmsg_payload_name_control \
         t63_recvmsg_header_fields t64_gettimeofday_timezone_untouched \
         t65_futex_wake_op_output t66_readv_iovec_overlap \
         t67_recvmsg_partial_error

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
