[bits 64]

; Input:
; eax    - Address to read/write
; ecx    - Value to write (only if STORE == 1)
; OPSIZE - {8, 16, 32} - Size of the operation to perform
; STORE  - {0, 1}      - Indicates if this is a load or a store operation
;
; Output:
; eax - Zero-extended loaded value (only if STORE == 0)
entry:
    ; Save the address to fetch
    mov ebx, eax

    ; Check alignment of access
%if OPSIZE == 8
%elif OPSIZE == 16
    test eax, 1
    jnz  .fault
%elif OPSIZE == 32
    test eax, 3
    jnz  .fault
%else
%error "Invalid OPSIZE"
%endif

    ; Subtract the base
    sub eax, BASE

    ; Make sure the address was not below BASE
    jb short .fault

    ; Bounds check against memory size
    cmp eax, MEMSIZE
    ja  short .fault

    ; Fetch the permissions
%if OPSIZE == 8
    movzx edx, byte [r10 + rax]
%elif OPSIZE == 16
    movzx edx, word [r10 + rax]
%elif OPSIZE == 32
    mov edx, dword [r10 + rax]
%else
%error "Invalid OPSIZE"
%endif

    ; Check permissions
    and edx, PERMS
    cmp edx, PERMS
    jne .fault

%if STORE == 0
    ; Everything is good, read the memory
%if OPSIZE == 8
    movzx eax, byte [r9 + rax]
%elif OPSIZE == 16
    movzx eax, word [r9 + rax]
%elif OPSIZE == 32
    mov eax, [r9 + rax]
%else
%error "Invalid OPSIZE"
%endif
%elif STORE == 1
    ; Update dirty bits
    mov  rdx, rax
    shr  rdx, 8     ; Divide by 256 to get dirty bit index
    bts  [r13], rdx ; Set the dirty bit

    ; Everything is good, store to memory
%if OPSIZE == 8
    mov byte [r9 + rax], cl
%elif OPSIZE == 16
    mov word [r9 + rax], cx
%elif OPSIZE == 32
    mov dword [r9 + rax], ecx
%else
%error "Invalid OPSIZE"
%endif
%else
%error "Invalid STORE"
%endif

    ; Operation was successful, go to next instruction!
    jmp short .good

.fault:
%if STORE == 0
    mov eax, READ_FAULT
%elif STORE == 1
    mov eax, WRITE_FAULT
%else
%error "Invalid STORE"
%endif
    ; Update PC
    mov dword [r8 + 32 * 4], PC

    ; Move the faulting address into ecx
    mov ecx, ebx
    ret

.good:

