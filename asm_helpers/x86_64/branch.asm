[bits 64]

; Input:
; eax - PC to branch to
entry:
    ; Save target PC
    mov dword [r8 + 32 * 4], eax

    ; Check if the target PC is 4-byte-aligned
    test eax, 3
    jnz  short .exec_fault

    ; Subtract the BASE
    sub eax, BASE

    ; Fail if we underflowed during the subtract
    jb short .exec_fault

    ; Divide by 4 to get the index into the JIT table entry
    shr eax, 2

    ; Bounds check against INSTRS
    cmp eax, INSTRS
    jae short .exec_fault

    ; Do the jump
    mov rax, [r11 + rax * 8]
    add rax, r12
    jmp rax

.exec_fault:
    mov eax, EXEC_FAULT
    ret

