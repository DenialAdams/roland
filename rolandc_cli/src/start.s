.text
.globl _start
.type _start, @function

_start:
    call __roland_entry
    ud2

.size _start, .-_start
