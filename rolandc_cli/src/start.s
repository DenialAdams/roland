.text
.globl _start
.type _start, @function

_start:
    # arch_prctl(ARCH_SHSTK_ENABLE, ARCH_SHSTK_SHSTK)
    mov $158, %eax
    mov $0x5001, %edi
    mov $1, %esi
    syscall

    test %rax, %rax
    js .Lcontinue

    # arch_prctl(ARCH_SHSTK_LOCK, ARCH_SHSTK_SHSTK)
    mov $158, %eax
    mov $0x5003, %edi
    mov $1, %esi
    syscall

.Lcontinue:
    call __roland_entry
    ud2

.size _start, .-_start
