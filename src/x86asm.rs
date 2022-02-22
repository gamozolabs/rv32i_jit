//! A very fully featured x86 assembler
//!
//! In reality, this is just supposed to be stupid fast and simple

#![cfg(target_arch = "x86_64")]

use crate::vm::{ExitStatus, Condition, Reg, Label, Perm, Assembler};

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
// dirty       - R13

/// A stream of assembled bytes
#[derive(Default, Clone)]
pub struct AsmStream<const BASE: u32, const MEMSIZE: usize,
                     const INSTRS: usize, const DIRTY: usize> {
    /// Raw assembled bytes
    bytes: Vec<u8>,

    /// Address of executable copy of `bytes`, established by `finalize`
    executable: Option<usize>,
}

/// Kinda gross, but here we load an assembly template and replace magic values
/// with JIT-time values
macro_rules! load_asm_template {
    ($template_path:expr, $base:expr, $instrs:expr,
     $memsize:expr, $perms:expr, $pc:expr) => {{
        // Get the template
        const TEMPLATE: &[u8] = include_bytes!($template_path);

        // Copy the template to a mutable array
        let mut bytes = [0u8; TEMPLATE.len()];
        bytes.copy_from_slice(TEMPLATE);

        // Go through each possible 4-byte offset looking for magic values
        for ii in 0..bytes.len() - 3 {
            let window = &mut bytes[ii..][..4];

            // Get the value
            let val = u32::from_le_bytes(window.try_into().unwrap());
            let replace = match val {
                0x776b0b67 => Some($base),
                0xfbbd3585 => Some($instrs as u32),
                0x44cd134a => Some(ExitStatus::ReadFault as u32),
                0xaf013de2 => Some(ExitStatus::WriteFault as u32),
                0x0dd0ff93 => Some(ExitStatus::ExecFault as u32),
                0x014e7958 => Some($memsize as u32),
                0xe714699d => Some($perms),
                0x74463054 => Some($pc),
                _          => None,
            };

            // Perform replacement of magic value
            if let Some(replace) = replace {
                window.copy_from_slice(&replace.to_le_bytes());
            }
        }

        // Return template
        bytes
    }}
}

impl<const BASE: u32, const MEMSIZE: usize, const INSTRS: usize,
     const DIRTY: usize>
        Assembler<BASE, MEMSIZE, INSTRS, DIRTY> for
        AsmStream<BASE, MEMSIZE, INSTRS, DIRTY> {
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
        dirty:     &mut [u8; DIRTY],
        jit_table: &[Label; INSTRS],
    ) -> (u32, u32) {
        // Get executable code address
        let exec = self.executable
            .expect("Attempted to enter JIT prior to finalizing assembly");

        // The generic A and B registres for the pseudo-architecture
        let (a, b): (u32, u32);

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
        in("r13") dirty.as_mut_ptr(),
        out("eax") a,
        out("ecx") b,
        out("edx") _);

        // Return a and b registers
        (a, b)
    }

    fn coverage_oneshot(&mut self, pc: u32) {
        /*
        entry:
            mov word [rel entry], 0x19eb
            mov eax, 0xdead0006
            mov ecx, 0x13371337
            mov [r8 + 32 * 4], ecx
            ret
        */

        let mut inst = [
            0x66, 0xc7, 0x05, 0xf7, 0xff, 0xff, 0xff, 0xeb,
            0x19, 0xb8, 0x06, 0x00, 0xad, 0xde, 0xb9, 0x37,
            0x13, 0x37, 0x13, 0x41, 0x89, 0x88, 0x80, 0x00,
            0x00, 0x00, 0xc3
        ];

        // Pad with nops until we're 2-byte aligned so we can ensure atomic
        // replacement of the first instruction with the branch
        while self.bytes.len() % 2 != 0 {
            self.bytes.push(0x90);
        }

        // Update exit code
        inst[0xa..][..4].copy_from_slice(
            &(ExitStatus::Coverage as u32).to_le_bytes());
        
        // Update exit PC
        inst[0xf..][..4].copy_from_slice(&pc.to_le_bytes());

        // Add the payload into the assembly stream
        self.bytes.extend_from_slice(&inst);
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
        // Load template
        let bytes = load_asm_template!("../asm_helpers/x86_64/branch.bin",
            BASE, INSTRS, MEMSIZE, 0, 0);
        self.bytes.extend_from_slice(&bytes);
    }

    fn read_reg(&mut self, reg: Reg, idx: u32) {
        assert!(idx < 33, "read_reg index out of bounds");

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
        assert!(idx < 33, "write_reg index out of bounds");

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
        // Load template
        let perms = u8::from_le_bytes([Perm::Read as u8; 1]) as u32;
        let bytes = load_asm_template!("../asm_helpers/x86_64/load8.bin",
            BASE, INSTRS, MEMSIZE - 1, perms, pc);
        self.bytes.extend_from_slice(&bytes);
    }

    fn load_u16_a(&mut self, pc: u32) {
        // Load template
        let perms = u16::from_le_bytes([Perm::Read as u8; 2]) as u32;
        let bytes = load_asm_template!("../asm_helpers/x86_64/load16.bin",
            BASE, INSTRS, MEMSIZE - 2, perms, pc);
        self.bytes.extend_from_slice(&bytes);
    }

    fn load_u32_a(&mut self, pc: u32) {
        // Load template
        let perms = u32::from_le_bytes([Perm::Read as u8; 4]) as u32;
        let bytes = load_asm_template!("../asm_helpers/x86_64/load32.bin",
            BASE, INSTRS, MEMSIZE - 4, perms, pc);
        self.bytes.extend_from_slice(&bytes);
    }

    fn store_u8_a_b(&mut self, pc: u32) {
        // Load template
        let perms = u8::from_le_bytes([Perm::Write as u8; 1]) as u32;
        let bytes = load_asm_template!("../asm_helpers/x86_64/store8.bin",
            BASE, INSTRS, MEMSIZE - 1, perms, pc);
        self.bytes.extend_from_slice(&bytes);
    }

    fn store_u16_a_b(&mut self, pc: u32) {
        // Load template
        let perms = u16::from_le_bytes([Perm::Write as u8; 2]) as u32;
        let bytes = load_asm_template!("../asm_helpers/x86_64/store16.bin",
            BASE, INSTRS, MEMSIZE - 2, perms, pc);
        self.bytes.extend_from_slice(&bytes);
    }

    fn store_u32_a_b(&mut self, pc: u32) {
        // Load template
        let perms = u32::from_le_bytes([Perm::Write as u8; 4]) as u32;
        let bytes = load_asm_template!("../asm_helpers/x86_64/store32.bin",
            BASE, INSTRS, MEMSIZE - 4, perms, pc);
        self.bytes.extend_from_slice(&bytes);
    }
}

