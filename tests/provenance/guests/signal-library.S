/* Preserve the supplied main data address through DSO -> main -> DSO calls.
 * No loads/stores or allocator models are needed to produce this diagnostic. */
.text
.globl signal_dso_outer
.type signal_dso_outer,@function
signal_dso_outer:
    subq $8, %rsp
    call *%rsi
    addq $8, %rsp
    ret
.size signal_dso_outer,.-signal_dso_outer

.globl signal_dso_leaf
.type signal_dso_leaf,@function
signal_dso_leaf:
    jmp *%rdi
.size signal_dso_leaf,.-signal_dso_leaf
.section .note.GNU-stack,"",@progbits
