//! A very fully featured x86 assembler
//!
//! In reality, this is just supposed to be stupid fast and simple

#![cfg(target_arch = "x86_64")]

use crate::{ExitStatus, Condition, Reg, Label, Perm};

// We allocate the pseudo-architecture registers as such:
//
// Reg::A - RAX
// Reg::B - RCX
//
// We use the following for scratch storage:
//
// RBX, RDX
//
// We allocate pointers to registers, memory, and permissions as such
//
// registers   - R8
// memory      - R9
// permissions - R10
// jit_table   - R11
// jit_base    - R12

/// A stream of assembled bytes
#[derive(Default)]
pub struct AsmStream<const BASE: u32, const MEMSIZE: usize,
                     const INSTRS: usize> {
    /// Raw assembled bytes
    bytes: Vec<u8>,

    /// Address of executable copy of `bytes`, established by `finalize`
    executable: Option<usize>,
}

impl<const BASE: u32, const MEMSIZE: usize, const INSTRS: usize>
        crate::Assembler<BASE, MEMSIZE, INSTRS> for
        AsmStream<BASE, MEMSIZE, INSTRS> {
    fn label(&mut self) -> Label {
        Label(self.bytes.len())
    }

    fn finalize(&mut self) {
        // Make sure we haven't finalized yet
        assert!(self.executable.is_none(), "Cannot finalize JIT twice");

        // Allocate RWX memory
        let rwx = unsafe {
            extern {
                fn mmap(addr: usize, length: usize, prot: i32, flags: i32,
                    fd: i32, offset: isize) -> usize;
            }

            // Ugh, crude but w/e
            let mem = mmap(0, self.bytes.len(), 7, 0x22, -1, 0);
            assert!((mem as isize) > 0, "mmap(RWX) failed");

            // Get a slice to the newly allocated memory
            std::slice::from_raw_parts_mut(mem as *mut u8, self.bytes.len())
        };

        // Copy in the bytes
        rwx.copy_from_slice(&self.bytes);

        // Set the executable address
        self.executable = Some(rwx.as_mut_ptr() as usize);

        // Clear the bytes so the `AsmStream` can cheaply be cloned
        self.bytes.clear();
    }

    unsafe fn enter_jit(
        &self,
        label:     Label,
        regs:      &mut [u32; 33],
        mem:       &mut [u8; MEMSIZE],
        perms:     &mut [u8; MEMSIZE],
        jit_table: &[Label; INSTRS],
    ) -> (u32, u32, u32) {
        // Get executable code address
        let exec = self.executable
            .expect("Attempted to enter JIT prior to finalizing assembly");

        // The generic A and B registres for the pseudo-architecture
        let (a, b): (u32, u32);

        // We clobber edx and use it for extra information on exits
        let edx: u32;

        std::arch::asm!(r#"
            // Manually save rbx
            push rbx

            call {entry}

            // Manually restore rbx
            pop  rbx
        "#,
        entry = in(reg) exec + label.0,
        in("r8") regs.as_mut_ptr(),
        in("r9") mem.as_mut_ptr(),
        in("r10") perms.as_mut_ptr(),
        in("r11") jit_table.as_ptr(),
        in("r12") exec,
        out("eax") a,
        out("ecx") b,
        out("edx") edx);

        // Return a and b registers
        (a, b, edx)
    }

    fn load_imm(&mut self, reg: Reg, val: u32) {
        match reg {
            Reg::A => {
                // mov eax, imm32
                self.bytes.push(0xb8); 
                self.bytes.extend_from_slice(&val.to_le_bytes());
            }
            Reg::B => {
                // mov ecx, imm32
                self.bytes.push(0xb9); 
                self.bytes.extend_from_slice(&val.to_le_bytes());
            }
        }
    }
    
    fn bcond_a_b(&mut self, cond: Condition, ttgt: u32, ftgt: u32) {
        /*
            cmp          eax, ecx
            mov          eax, TTGT
            mov          ecx, FTGT
            cmovn[e,l,b] eax, ecx
        */
        let mut inst = [
            0x39, 0xc8, 0xb8, 0xef, 0xbe, 0xad, 0xde, 0xb9,
            0xef, 0xbe, 0xad, 0xde, 0x0f, 0x45, 0xc1
        ];

        // Set the true and false targets
        inst[3..][..4].copy_from_slice(&ttgt.to_le_bytes());
        inst[8..][..4].copy_from_slice(&ftgt.to_le_bytes());

        // Determine the condition byte
        let cond = match cond {
            Condition::Eq  => 0x45, // cmovne
            Condition::Lt  => 0x4d, // cmovnl
            Condition::Ltu => 0x43, // cmovnb
        };

        // Update instruction to reflect the condition
        inst[0xd] = cond;

        // Push the instruction, and then branch to A
        self.bytes.extend_from_slice(&inst);
        self.branch_a();
    }
    
    fn branch_a(&mut self) {
        /*
            ; Save the PC
            mov ecx, eax

            ; Check if the target PC is 4-byte-aligned
            test eax, 3
            jnz  short fail

            ; Subtract the BASE
            sub eax, 0xdeadbeef

            ; Fail if we underflowed during the subtract
            jb short fail

            ; Divide by 4 to get the index into the JIT table entry
            shr eax, 2

            ; Bounds check against INSTRS
            cmp eax, 0xdeadbeef
            jae short fail

            ; Do the jump
            mov rax, [r11 + rax * 8]
            add rax, r12
            jmp rax

            fail:
            mov eax, 0xdead0000
            ret
        */

        let mut inst = [
            0x89, 0xc1, 0xa9, 0x03, 0x00, 0x00, 0x00, 0x75,
            0x1a, 0x2d, 0xef, 0xbe, 0xad, 0xde, 0x72, 0x13,
            0xc1, 0xe8, 0x02, 0x3d, 0xef, 0xbe, 0xad, 0xde,
            0x73, 0x09, 0x49, 0x8b, 0x04, 0xc3, 0x4c, 0x01,
            0xe0, 0xff, 0xe0, 0xb8, 0x00, 0x00, 0xad, 0xde,
            0xc3
        ];

        // Insert the base
        inst[0xa..][..4].copy_from_slice(&BASE.to_le_bytes());

        // Insert the INSTRS
        inst[0x14..][..4].copy_from_slice(&(INSTRS as u32).to_le_bytes());
        
        // Insert the ExecFault exit status
        inst[0x24..][..4].copy_from_slice(
            &(ExitStatus::ExecFault as u32).to_le_bytes());

        // Place the bytes into the stream
        self.bytes.extend_from_slice(&inst);
    }

    fn read_reg(&mut self, reg: Reg, idx: u32) {
        assert!(idx < 32, "read_reg index out of bounds");
       
        if idx != 0 {
            match reg {
                Reg::A => {
                    // mov eax, [r8 + imm32]
                    self.bytes.extend_from_slice(&[0x41, 0x8b, 0x80]);
                    self.bytes.extend_from_slice(&(idx * 4).to_le_bytes());
                }
                Reg::B => {
                    // mov ecx, [r8 + imm32]
                    self.bytes.extend_from_slice(&[0x41, 0x8b, 0x88]);
                    self.bytes.extend_from_slice(&(idx * 4).to_le_bytes());
                }
            }
        } else {
            // Reading the zero register
            match reg {
                // xor eax, eax
                Reg::A => self.bytes.extend_from_slice(&[0x31, 0xc0]),

                // xor ecx, ecx
                Reg::B => self.bytes.extend_from_slice(&[0x31, 0xc9]),
            }
        }
    }
    
    fn slt_a_b(&mut self) {
        // cmp  eax, ecx
        // mov  eax, 0
        // setl al
        self.bytes.extend_from_slice(&[
            0x39, 0xc8, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x9c, 0xc0
        ]);
    }
    
    fn sltu_a_b(&mut self) {
        // cmp  eax, ecx
        // mov  eax, 0
        // setb al
        self.bytes.extend_from_slice(&[
            0x39, 0xc8, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x92, 0xc0
        ]);
    }
    
    fn swap_a_b(&mut self) {
        // xchg eax, ecx
        self.bytes.push(0x91);
    }
    
    fn add_a_b(&mut self) {
        // add eax, ecx
        self.bytes.extend_from_slice(&[0x01, 0xc8]);
    }
    
    fn sub_a_b(&mut self) {
        // sub eax, ecx
        self.bytes.extend_from_slice(&[0x29, 0xc8]);
    }
    
    fn xor_a_b(&mut self) {
        // xor eax, ecx
        self.bytes.extend_from_slice(&[0x31, 0xc8]);
    }
    
    fn or_a_b(&mut self) {
        // or eax, ecx
        self.bytes.extend_from_slice(&[0x09, 0xc8]);
    }
    
    fn and_a_b(&mut self) {
        // and eax, ecx
        self.bytes.extend_from_slice(&[0x21, 0xc8]);
    }
    
    fn shl_a_b(&mut self) {
        // shl eax, cl
        self.bytes.extend_from_slice(&[0xd3, 0xe0]);
    }
    
    fn shr_a_b(&mut self) {
        // shr eax, cl
        self.bytes.extend_from_slice(&[0xd3, 0xe8]);
    }
    
    fn sar_a_b(&mut self) {
        // sar eax, cl
        self.bytes.extend_from_slice(&[0xd3, 0xf8]);
    }
    
    fn write_reg(&mut self, idx: u32, reg: Reg) {
        assert!(idx != 0, "write_reg to the zero register is pointless");
        assert!(idx < 32, "write_reg index out of bounds");

        match reg {
            Reg::A => {
                // mov [r8 + imm32], eax
                self.bytes.extend_from_slice(&[0x41, 0x89, 0x80]);
                self.bytes.extend_from_slice(&(idx * 4).to_le_bytes());
            }
            Reg::B => {
                // mov [r8 + imm32], ecx
                self.bytes.extend_from_slice(&[0x41, 0x89, 0x88]);
                self.bytes.extend_from_slice(&(idx * 4).to_le_bytes());
            }
        }
    }

    fn ret(&mut self) {
        self.bytes.push(0xc3);
    }
    
    fn sex_u8_a(&mut self) {
        // movsx eax, al
        self.bytes.extend_from_slice(&[0x0f, 0xbe, 0xc0]);
    }
    
    fn sex_u16_a(&mut self) {
        // movsx eax, ax
        self.bytes.extend_from_slice(&[0x0f, 0xbf, 0xc0]);
    }
    
    fn load_u8_a(&mut self, pc: u32) {
        /*
            ; Save the address to fetch
            mov ecx, eax

            ; Subtract the base
            sub eax, 0xdeadbeef

            ; Handle errors
            jb short fail

            ; Bounds check against memory size
            cmp eax, 0xdeadbeef
            jae short fail

            ; Fetch the permissions
            movzx edx, byte [r10 + rax]

            ; Check permissions
            and edx, 0xdeadbeef
            cmp edx, 0xdeadbeef
            jne fail

            ; Everything is good, read the memory
            movzx eax, byte [r9 + rax]
            jmp short good

            fail:
                mov eax, 0xdead0002
                mov edx, 0xdeadbeef ; Faulting PC
                ret

            good:
        */
        let mut inst = [
            0x89, 0xc1, 0x2d, 0xef, 0xbe, 0xad, 0xde, 0x72,
            0x21, 0x3d, 0xef, 0xbe, 0xad, 0xde, 0x73, 0x1a,
            0x41, 0x0f, 0xb6, 0x14, 0x02, 0x81, 0xe2, 0xef,
            0xbe, 0xad, 0xde, 0x81, 0xfa, 0xef, 0xbe, 0xad,
            0xde, 0x75, 0x07, 0x41, 0x0f, 0xb6, 0x04, 0x01,
            0xeb, 0x0b, 0xb8, 0x02, 0x00, 0xad, 0xde, 0xba,
            0xef, 0xbe, 0xad, 0xde, 0xc3
        ];

        // Insert the base
        inst[3..][..4].copy_from_slice(&BASE.to_le_bytes());
        
        // Insert the memory size
        inst[0xa..][..4].copy_from_slice(&(MEMSIZE as u32).to_le_bytes());
        
        // Insert permission mask
        let perms = u8::from_le_bytes([Perm::Read as u8; 1]) as u32;
        inst[0x17..][..4].copy_from_slice(&perms.to_le_bytes());
        inst[0x1d..][..4].copy_from_slice(&perms.to_le_bytes());
        
        // Insert exit status
        inst[0x2b..][..4].copy_from_slice(
            &(ExitStatus::ReadFault as u32).to_le_bytes());

        // Insert faulting PC
        inst[0x30..][..4].copy_from_slice(&pc.to_le_bytes());

        // Place the bytes into the stream
        self.bytes.extend_from_slice(&inst);
    }
    
    fn load_u16_a(&mut self, pc: u32) {
        /*
            ; Save the address to fetch
            mov ecx, eax

            ; Subtract the base
            sub eax, 0xdeadbeef

            ; Handle errors
            jb short fail

            ; Bounds check against memory size
            cmp eax, 0xdeadbeef
            jae short fail

            ; Fetch the permissions
            movzx edx, word [r10 + rax]

            ; Check permissions
            and edx, 0xdeadbeef
            cmp edx, 0xdeadbeef
            jne fail

            ; Everything is good, read the memory
            movzx eax, word [r9 + rax]
            jmp short good

            fail:
                mov eax, 0xdead0002
                mov edx, 0xdeadbeef ; Faulting PC
                ret

            good:
        */
        let mut inst = [
            0x89, 0xc1, 0x2d, 0xef, 0xbe, 0xad, 0xde, 0x72,
            0x21, 0x3d, 0xef, 0xbe, 0xad, 0xde, 0x73, 0x1a,
            0x41, 0x0f, 0xb7, 0x14, 0x02, 0x81, 0xe2, 0xef,
            0xbe, 0xad, 0xde, 0x81, 0xfa, 0xef, 0xbe, 0xad,
            0xde, 0x75, 0x07, 0x41, 0x0f, 0xb7, 0x04, 0x01,
            0xeb, 0x0b, 0xb8, 0x02, 0x00, 0xad, 0xde, 0xba,
            0xef, 0xbe, 0xad, 0xde, 0xc3
        ];

        // Insert the base
        inst[3..][..4].copy_from_slice(&BASE.to_le_bytes());
        
        // Insert the memory size
        inst[0xa..][..4].copy_from_slice(&(MEMSIZE as u32 - 1).to_le_bytes());
        
        // Insert permission mask
        let perms = u16::from_le_bytes([Perm::Read as u8; 2]) as u32;
        inst[0x17..][..4].copy_from_slice(&perms.to_le_bytes());
        inst[0x1d..][..4].copy_from_slice(&perms.to_le_bytes());
        
        // Insert exit status
        inst[0x2b..][..4].copy_from_slice(
            &(ExitStatus::ReadFault as u32).to_le_bytes());

        // Insert faulting PC
        inst[0x30..][..4].copy_from_slice(&pc.to_le_bytes());

        // Place the bytes into the stream
        self.bytes.extend_from_slice(&inst);
    }

    fn load_u32_a(&mut self, pc: u32) {
        /*
            ; Save the address to fetch
            mov ecx, eax

            ; Subtract the base
            sub eax, 0xdeadbeef

            ; Handle errors
            jb short fail

            ; Bounds check against memory size
            cmp eax, 0xdeadbeef
            jae short fail

            ; Fetch the permissions
            mov edx, [r10 + rax]

            ; Check permissions
            and edx, 0xdeadbeef
            cmp edx, 0xdeadbeef
            jne fail

            ; Everything is good, read the memory
            mov eax, [r9 + rax]
            jmp short good

            fail:
                mov eax, 0xdead0002
                mov edx, 0xdeadbeef ; Faulting PC
                ret

            good:
        */
        let mut inst = [
            0x89, 0xc1, 0x2d, 0xef, 0xbe, 0xad, 0xde, 0x72,
            0x1f, 0x3d, 0xef, 0xbe, 0xad, 0xde, 0x73, 0x18,
            0x41, 0x8b, 0x14, 0x02, 0x81, 0xe2, 0xef, 0xbe,
            0xad, 0xde, 0x81, 0xfa, 0xef, 0xbe, 0xad, 0xde,
            0x75, 0x06, 0x41, 0x8b, 0x04, 0x01, 0xeb, 0x0b,
            0xb8, 0x02, 0x00, 0xad, 0xde, 0xba, 0xef, 0xbe,
            0xad, 0xde, 0xc3
        ];

        // Insert the base
        inst[3..][..4].copy_from_slice(&BASE.to_le_bytes());
        
        // Insert the memory size
        inst[0xa..][..4].copy_from_slice(&(MEMSIZE as u32 - 3).to_le_bytes());
        
        // Insert permission mask
        let perms = u32::from_le_bytes([Perm::Read as u8; 4]);
        inst[0x16..][..4].copy_from_slice(&perms.to_le_bytes());
        inst[0x1c..][..4].copy_from_slice(&perms.to_le_bytes());
        
        // Insert exit status
        inst[0x29..][..4].copy_from_slice(
            &(ExitStatus::ReadFault as u32).to_le_bytes());

        // Insert faulting PC
        inst[0x2e..][..4].copy_from_slice(&pc.to_le_bytes());
        
        // Place the bytes into the stream
        self.bytes.extend_from_slice(&inst);
    }
    
    fn store_u8_a_b(&mut self, pc: u32) {
        /*
            ; Save the address to write to
            mov ebx, eax

            ; Subtract the base
            sub eax, 0xdeadbeef

            ; Handle errors
            jb short fail

            ; Bounds check against memory size
            cmp eax, 0xdeadbeef
            jae short fail

            ; Fetch the permissions
            movzx edx, byte [r10 + rax]

            ; Check permissions
            and edx, 0xdeadbeef
            cmp edx, 0xdeadbeef
            jne fail

            ; Everything is good, write the memory
            mov [r9 + rax], cl

            fail:
                mov eax, 0xdead0003
                mov ecx, ebx        ; Faulting address
                mov edx, 0xdeadbeef ; Faulting PC
                ret

            good:
        */
        let mut inst = [
            0x89, 0xc3, 0x2d, 0xef, 0xbe, 0xad, 0xde, 0x72,
            0x1e, 0x3d, 0xef, 0xbe, 0xad, 0xde, 0x73, 0x17,
            0x41, 0x0f, 0xb6, 0x14, 0x02, 0x81, 0xe2, 0xef,
            0xbe, 0xad, 0xde, 0x81, 0xfa, 0xef, 0xbe, 0xad,
            0xde, 0x75, 0x04, 0x41, 0x88, 0x0c, 0x01, 0xb8,
            0x03, 0x00, 0xad, 0xde, 0x89, 0xd9, 0xba, 0xef,
            0xbe, 0xad, 0xde, 0xc3
        ];
        
        // Insert the base
        inst[3..][..4].copy_from_slice(&BASE.to_le_bytes());
        
        // Insert the memory size
        inst[0xa..][..4].copy_from_slice(&(MEMSIZE as u32).to_le_bytes());
        
        // Insert permission mask
        let perms = u8::from_le_bytes([Perm::Write as u8; 1]) as u32;
        inst[0x17..][..4].copy_from_slice(&perms.to_le_bytes());
        inst[0x1d..][..4].copy_from_slice(&perms.to_le_bytes());
        
        // Insert exit status
        inst[0x28..][..4].copy_from_slice(
            &(ExitStatus::WriteFault as u32).to_le_bytes());

        // Insert faulting PC
        inst[0x2f..][..4].copy_from_slice(&pc.to_le_bytes());
        
        // Place the bytes into the stream
        self.bytes.extend_from_slice(&inst);
    }
    
    fn store_u16_a_b(&mut self, pc: u32) {
        /*
            ; Save the address to write to
            mov ebx, eax

            ; Subtract the base
            sub eax, 0xdeadbeef

            ; Handle errors
            jb short fail

            ; Bounds check against memory size
            cmp eax, 0xdeadbeef
            jae short fail

            ; Fetch the permissions
            movzx edx, word [r10 + rax]

            ; Check permissions
            and edx, 0xdeadbeef
            cmp edx, 0xdeadbeef
            jne fail

            ; Everything is good, write the memory
            mov [r9 + rax], cx

            fail:
                mov eax, 0xdead0003
                mov ecx, ebx        ; Faulting address
                mov edx, 0xdeadbeef ; Faulting PC
                ret

            good:
        */
        let mut inst = [
            0x89, 0xc3, 0x2d, 0xef, 0xbe, 0xad, 0xde, 0x72,
            0x1f, 0x3d, 0xef, 0xbe, 0xad, 0xde, 0x73, 0x18,
            0x41, 0x0f, 0xb7, 0x14, 0x02, 0x81, 0xe2, 0xef,
            0xbe, 0xad, 0xde, 0x81, 0xfa, 0xef, 0xbe, 0xad,
            0xde, 0x75, 0x05, 0x66, 0x41, 0x89, 0x0c, 0x01,
            0xb8, 0x03, 0x00, 0xad, 0xde, 0x89, 0xd9, 0xba,
            0xef, 0xbe, 0xad, 0xde, 0xc3
        ];
        
        // Insert the base
        inst[3..][..4].copy_from_slice(&BASE.to_le_bytes());
        
        // Insert the memory size
        inst[0xa..][..4].copy_from_slice(&(MEMSIZE as u32 - 1).to_le_bytes());
        
        // Insert permission mask
        let perms = u16::from_le_bytes([Perm::Write as u8; 2]) as u32;
        inst[0x17..][..4].copy_from_slice(&perms.to_le_bytes());
        inst[0x1d..][..4].copy_from_slice(&perms.to_le_bytes());
        
        // Insert exit status
        inst[0x29..][..4].copy_from_slice(
            &(ExitStatus::WriteFault as u32).to_le_bytes());

        // Insert faulting PC
        inst[0x30..][..4].copy_from_slice(&pc.to_le_bytes());
        
        // Place the bytes into the stream
        self.bytes.extend_from_slice(&inst);
    }
    
    fn store_u32_a_b(&mut self, pc: u32) {
        /*
            ; Save the address to write to
            mov ebx, eax

            ; Subtract the base
            sub eax, 0xdeadbeef

            ; Handle errors
            jb short fail

            ; Bounds check against memory size
            cmp eax, 0xdeadbeef
            jae short fail

            ; Fetch the permissions
            mov edx, dword [r10 + rax]

            ; Check permissions
            and edx, 0xdeadbeef
            cmp edx, 0xdeadbeef
            jne fail

            ; Everything is good, write the memory
            mov [r9 + rax], ecx

            fail:
                mov eax, 0xdead0003
                mov ecx, ebx        ; Faulting address
                mov edx, 0xdeadbeef ; Faulting PC
                ret

            good:
        */
        let mut inst = [
            0x89, 0xc3, 0x2d, 0xef, 0xbe, 0xad, 0xde, 0x72,
            0x1d, 0x3d, 0xef, 0xbe, 0xad, 0xde, 0x73, 0x16,
            0x41, 0x8b, 0x14, 0x02, 0x81, 0xe2, 0xef, 0xbe,
            0xad, 0xde, 0x81, 0xfa, 0xef, 0xbe, 0xad, 0xde,
            0x75, 0x04, 0x41, 0x89, 0x0c, 0x01, 0xb8, 0x03,
            0x00, 0xad, 0xde, 0x89, 0xd9, 0xba, 0xef, 0xbe,
            0xad, 0xde, 0xc3
        ];
        
        // Insert the base
        inst[3..][..4].copy_from_slice(&BASE.to_le_bytes());
        
        // Insert the memory size
        inst[0xa..][..4].copy_from_slice(&(MEMSIZE as u32 - 3).to_le_bytes());
        
        // Insert permission mask
        let perms = u32::from_le_bytes([Perm::Write as u8; 4]);
        inst[0x16..][..4].copy_from_slice(&perms.to_le_bytes());
        inst[0x1c..][..4].copy_from_slice(&perms.to_le_bytes());
        
        // Insert exit status
        inst[0x27..][..4].copy_from_slice(
            &(ExitStatus::WriteFault as u32).to_le_bytes());

        // Insert faulting PC
        inst[0x2e..][..4].copy_from_slice(&pc.to_le_bytes());
        
        // Place the bytes into the stream
        self.bytes.extend_from_slice(&inst);
    }
}

