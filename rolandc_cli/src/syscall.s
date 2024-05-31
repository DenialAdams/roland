.text

.global syscall0
syscall0:
	movq %rdi, %rax
	syscall
	ret


.global syscall1
syscall1:
	movq %rdi, %rax
	movq %rsi, %rdi
	syscall
	ret


.global syscall2
syscall2:
	movq %rdi, %rax
	movq %rsi, %rdi
	movq %rdx, %rsi
	syscall
	ret


.global syscall3
syscall3:
	movq %rdi, %rax
	movq %rsi, %rdi
	movq %rdx, %rsi
	movq %rcx, %rdx
	syscall
	ret


.global syscall4
syscall4:
	movq %rdi, %rax
	movq %r8, %r10
	movq %rsi, %rdi
	movq %rdx, %rsi
	movq %rcx, %rdx
	syscall
	ret


.global syscall5
syscall5:
	movq %rdi, %rax
	movq %r8, %r10
	movq %rsi, %rdi
	movq %r9, %r8
	movq %rdx, %rsi
	movq %rcx, %rdx
	syscall
	ret


.global syscall6
syscall6:
	movq %rdi, %rax
	movq %r8, %r10
	movq %rsi, %rdi
	movq %r9, %r8
	movq %rdx, %rsi
	movq 8(%rsp), %r9
	movq %rcx, %rdx
	syscall
