.text
.globl coverage_span
.type coverage_span,@function
coverage_span:
    nop
    nop
.globl coverage_access_pc
coverage_access_pc:
    movq 4(%rdi), %rax
    ret
.size coverage_span, .-coverage_span
.globl coverage_signal
.type coverage_signal,@function
coverage_signal:
    xorl %eax, %eax
.globl coverage_signal_pc
coverage_signal_pc:
    movq (%rax), %rax
    ret
.size coverage_signal, .-coverage_signal

# Return runtime addresses without executable COPY relocations for DSO labels.
.globl coverage_access_address
.type coverage_access_address,@function
coverage_access_address:
    movq coverage_access_pc@GOTPCREL(%rip), %rax
    ret
.size coverage_access_address, .-coverage_access_address
.globl coverage_signal_address
.type coverage_signal_address,@function
coverage_signal_address:
    movq coverage_signal_pc@GOTPCREL(%rip), %rax
    ret
.size coverage_signal_address, .-coverage_signal_address

# The no-CRT entry tail-jumps here with no live main return boundary.
.globl coverage_no_caller
.type coverage_no_caller,@function
coverage_no_caller:
    subq $8, %rsp
    call coverage_span
    movl %eax, %edi
    movl $60, %eax
    syscall
.size coverage_no_caller, .-coverage_no_caller
.section .note.GNU-stack,"",@progbits
