.text
.globl coverage_nested
.type coverage_nested,@function
coverage_nested:
    subq $8, %rsp
    call coverage_span@PLT
.globl coverage_inner_return
coverage_inner_return:
    addq $8, %rsp
    ret
.size coverage_nested, .-coverage_nested

.globl coverage_callback
.type coverage_callback,@function
coverage_callback:
    subq $8, %rsp
    call *%rsi
    addq $8, %rsp
    ret
.size coverage_callback, .-coverage_callback

.globl coverage_inner_return_address
.type coverage_inner_return_address,@function
coverage_inner_return_address:
    movq coverage_inner_return@GOTPCREL(%rip), %rax
    ret
.size coverage_inner_return_address, .-coverage_inner_return_address
.section .note.GNU-stack,"",@progbits
