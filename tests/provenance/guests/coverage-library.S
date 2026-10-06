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
.section .note.GNU-stack,"",@progbits
