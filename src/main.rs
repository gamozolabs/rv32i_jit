//! An extremely basic RISC-V (rv32i) emulator

#![feature(array_chunks)]

mod x86asm;

use std::path::Path;

/// Wrapper around [`Error`]
type Result<T> = std::result::Result<T, Error>;

/// Error types for this crate
#[derive(Debug)]
enum Error {
    /// Failed to read FELF from disk
    FelfRead(std::io::Error),

    /// FELF had a malformed header
    InvalidFelf,

    /// FELF could not be loaded in the virtual memory region created for the
    /// VM
    FelfOutOfRange,

    /// VMs `BASE` must be 32-bit aligned
    BadAlignment,

    /// VMs `MEMSIZE` must be a power of two and >= 4
    BadMemSize,

    /// VMs `BASE` + `MEMSIZE` must be <= 2**32
    TooMuchRam,

    /// A `usize` value or `u64` value which was expected to fit into a `u32`
    /// failed to fit
    IntegerTruncation,

    /// Memory exists which is executable and also writable, which is not
    /// supported
    NoDynamicCode,

    /// Due to limitations of Rust const generics, we expect the user to give
    /// the number of instructions based on `MEMSIZE`, this is always just
    /// `MEMSIZE / 4`, and thus if it doesn't match that, you get this error
    InvalidInstructionCount,
}

/// A label which references an assembly location
#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
struct Label(usize);

/// Registers for the pseudo-architecture we use for the assembler
enum Reg {
    /// The A register!
    A,

    /// The B register!
    B,
}

/// Condition codes for conditional branches
enum Condition {
    /// Equal
    Eq,

    /// Signed less than
    Lt,

    /// Unsigned less than
    Ltu,
}

/// A trait defining the basic operations of an assembler
trait Assembler<const BASE: u32, const MEMSIZE: usize,
                const INSTRS: usize>: Default {
    /// Create a label for the current location in the assembly stream
    fn label(&mut self) -> Label;

    /// Copy the JIT into executable memory
    fn finalize(&mut self);

    /// Start executing the JIT at `label` and return the pseudo-architecture
    /// A and B registers
    unsafe fn enter_jit(
        &self,
        label:     Label,
        regs:      &mut [u32; 33],
        mem:       &mut [u8; MEMSIZE],
        perms:     &mut [u8; MEMSIZE],
        jit_table: &[Label; INSTRS],
    ) -> (u32, u32, u32);

    /// Emit a load immediate into a register
    fn load_imm(&mut self, reg: Reg, val: u32);

    /// Branch indirectly to the PC in `Reg::A`
    fn branch_a(&mut self);

    /// Read the target-architecture register at `idx` and store it into the
    /// pseudo-architecture `reg`
    fn read_reg(&mut self, reg: Reg, idx: u32);

    /// Write the pseudo-architecture `reg` into the target-architecture
    /// register at `idx`
    fn write_reg(&mut self, idx: u32, reg: Reg);

    /// Branch to `ttgt` if `Reg::A` == `Reg::B` otherwise branch to `ftgt`
    fn bcond_a_b(&mut self, cond: Condition, ttgt: u32, ftgt: u32);

    /// Swap registers `Reg::A` and `Reg::B`
    fn swap_a_b(&mut self);

    /// `Reg::A = if Reg::A s< Reg::B { 1 } else { 0 }`
    fn slt_a_b(&mut self);

    /// `Reg::A = if Reg::A u< Reg::B { 1 } else { 0 }`
    fn sltu_a_b(&mut self);

    /// `Reg::A = Reg::A + Reg::B`
    fn add_a_b(&mut self);

    /// `Reg::A = Reg::A - Reg::B`
    fn sub_a_b(&mut self);

    /// `Reg::A = Reg::A ^ Reg::B`
    fn xor_a_b(&mut self);

    /// `Reg::A = Reg::A | Reg::B`
    fn or_a_b(&mut self);

    /// `Reg::A = Reg::A & Reg::B`
    fn and_a_b(&mut self);

    /// `Reg::A = Reg::A u<< Reg::B`
    fn shl_a_b(&mut self);

    /// `Reg::A = Reg::A u>> Reg::B`
    fn shr_a_b(&mut self);

    /// `Reg::A = Reg::A s>> Reg::B`
    fn sar_a_b(&mut self);

    /// `Reg::A = sign_extend8(Reg::A)`
    fn sex_u8_a(&mut self);

    /// `Reg::A = sign_extend16(Reg::A)`
    fn sex_u16_a(&mut self);

    /// Load the memory pointed to by `Reg::A` into `Reg::A` and interpret
    /// it as a `u8`
    /// PC is the address of this instruction, for exception reporting
    fn load_u8_a(&mut self, pc: u32);

    /// Load the memory pointed to by `Reg::A` into `Reg::A` and interpret
    /// it as a `u16`
    /// PC is the address of this instruction, for exception reporting
    fn load_u16_a(&mut self, pc: u32);

    /// Load the memory pointed to by `Reg::A` into `Reg::A` and interpret
    /// it as a `u32`
    /// PC is the address of this instruction, for exception reporting
    fn load_u32_a(&mut self, pc: u32);

    /// Store the 8-bit value in `Reg::B` into the address at `Reg::A`
    /// PC is the address of this instruction, for exception reporting
    fn store_u8_a_b(&mut self, pc: u32);

    /// Store the 16-bit value in `Reg::B` into the address at `Reg::A`
    /// PC is the address of this instruction, for exception reporting
    fn store_u16_a_b(&mut self, pc: u32);

    /// Store the 32-bit value in `Reg::B` into the address at `Reg::A`
    /// PC is the address of this instruction, for exception reporting
    fn store_u32_a_b(&mut self, pc: u32);

    /// Emit a return instruction to exit the JIT
    fn ret(&mut self);
}

/// Different types of memory faults
enum MemoryFault {
    /// Failed to read `bytes` at `vaddr`
    Read { vaddr: u32, bytes: u8 },

    /// Failed to execute `bytes` at `vaddr`
    Exec { vaddr: u32, bytes: u8 },

    /// Failed to write `bytes` at `vaddr`
    Write { vaddr: u32, bytes: u8 },
}

/// A guest virtual machine
struct Vm<ASM: Assembler<BASE, MEMSIZE, INSTRS>,
          const BASE: u32, const MEMSIZE: usize, const INSTRS: usize> {
    /// VM GPR register state + PC
    regs: [u32; 33],

    /// Backing memory for the VM
    memory: Box<[u8; MEMSIZE]>,

    /// Backing permissions for the VM
    perms: Box<[u8; MEMSIZE]>,

    /// Lookup table from all possible instructions to JIT labels
    jit_table: Box<[Label; INSTRS]>,

    /// Assembler which holds the JITted code
    asm: ASM,
}

/// Permission bit flags
#[repr(u8)]
enum Perm {
    /// Execute permissions
    Exec = 0x01,

    /// Write permissions
    Write = 0x02,

    /// Read permissions
    Read = 0x04,
}

/// JIT exit statuses
#[repr(u32)]
enum ExitStatus {
    /// Attempted to execute non-executable code
    /// This also is triggered if a branch to a non-4-byte-aligned instruction
    /// occurs
    /// B register contains PC of faulting instruction
    ExecFault = 0xdead0000,

    /// Attempted to execute an instruction which is invalid
    /// B register contains PC of invalid instruction
    InvalidOpcode = 0xdead0001,

    /// Attempted to read memory without read permissions
    ReadFault = 0xdead0002,

    /// Attempted to write memory without write permissions
    WriteFault = 0xdead0003,
}

impl<ASM: Assembler<BASE, MEMSIZE, INSTRS>,
     const BASE: u32, const MEMSIZE: usize, const INSTRS: usize>
        Vm<ASM, BASE, MEMSIZE, INSTRS> {
    /// Create a VM from a FELF
    fn from_felf(felf: impl AsRef<Path>) -> Result<Self> {
        // VMs must have a 32-bit aligned base
        if BASE & 0x3 != 0 {
            return Err(Error::BadAlignment);
        }

        // VMs must have a power-of-two memory size so we can use masks instead
        // of modulo bounds checks
        if MEMSIZE.count_ones() != 1 || MEMSIZE < 4 {
            return Err(Error::BadMemSize);
        }

        // Memory must not exceed a 32-bit address space
        let endmem = BASE.try_into().ok()
            .and_then(|x: usize| x.checked_add(MEMSIZE));
        if endmem.is_none() || endmem.unwrap() > 0x1_0000_0000 {
            return Err(Error::TooMuchRam);
        }

        // Make sure instruction count is accurate
        if MEMSIZE / 4 != INSTRS {
            return Err(Error::InvalidInstructionCount);
        }

        // Read the FELF into memory
        let felf = std::fs::read(felf).map_err(Error::FelfRead)?;

        // FELF header is 0x18 bytes
        if felf.len() < 0x18 || &felf[..8] != b"FELF0002" {
            return Err(Error::InvalidFelf);
        }

        // Get the FELF entry point and base
        let entry: u32 =
            u64::from_le_bytes(felf[0x08..][..8].try_into().unwrap())
            .try_into().map_err(|_| Error::IntegerTruncation)?;
        let base: u32 =
            u64::from_le_bytes(felf[0x10..][..8].try_into().unwrap())
            .try_into().map_err(|_| Error::IntegerTruncation)?;

        // Get the payload
        let payload = &felf[0x18..];

        // Get the memory and the permissions as separate
        let memory = &payload[..payload.len() / 2];
        let perms  = &payload[payload.len() / 2..];

        // Create empty memory and permissions
        let mut raw_memory: Box<[u8; MEMSIZE]> =
            vec![0u8; MEMSIZE].into_boxed_slice().try_into().unwrap();
        let mut raw_perms: Box<[u8; MEMSIZE]> =
            vec![0u8; MEMSIZE].into_boxed_slice().try_into().unwrap();

        // Get the slice to memory where the FELF should be placed
        let offset =
            base.checked_sub(BASE).ok_or(Error::FelfOutOfRange)? as usize;
        let memory_slice = raw_memory
            .get_mut(offset..offset + memory.len())
            .ok_or(Error::FelfOutOfRange)?;
        let perms_slice = raw_perms
            .get_mut(offset..offset + perms.len())
            .ok_or(Error::FelfOutOfRange)?;

        // Update the memory and permissions from the FELF
        memory_slice.copy_from_slice(memory);
        perms_slice.copy_from_slice(perms);

        // Create empty JIT table mapping
        let jit_table: Box<[Label; INSTRS]> =
            vec![Label(0); INSTRS].into_boxed_slice().try_into().unwrap();

        // Create registers
        let mut regs = [0u32; 33];
        regs[32] = entry;

        // Return the clean VM state
        Ok(Self {
            memory: raw_memory,
            perms:  raw_perms,
            asm:    ASM::default(),
            jit_table,
            regs,
        })
    }

    /// JIT all the instructions in the VM, I guess it's not actually a JIT
    /// but a translation but too bad
    fn jit(&mut self) -> Result<()> {
        /// Writable permission mask
        const WRITE: u32 = u32::from_le_bytes([Perm::Write as u8; 4]);

        /// Executable permission mask
        const EXEC: u32 = u32::from_le_bytes([Perm::Exec as u8; 4]);

        // Go through each possible instruction in memory
        for (inst_idx, (mem, perms)) in self.memory.array_chunks::<4>()
                .zip(self.perms.array_chunks::<4>()).enumerate() {
            // Compute the program counter for this instruction
            let pc = BASE + (inst_idx as u32) * 4;

            // Get the permissions for this instruction
            let perms = u32::from_le_bytes(*perms);

            // Make sure this memory is fully executable, but also not writable
            // as we do not support self-modifying code
            let executable = perms & EXEC  == EXEC;
            let any_write  = perms & WRITE != 0;

            // We do not allow executable and writable memory
            if executable && any_write {
                return Err(Error::NoDynamicCode);
            }

            // Update JIT table
            self.jit_table[inst_idx] = self.asm.label();

            // If it's not executable, emit the execution fault code
            if !executable {
                self.asm.load_imm(Reg::A, ExitStatus::ExecFault as u32);
                self.asm.load_imm(Reg::B, pc);
                self.asm.ret();
                continue;
            }

            // Yay, we have an executable instruction! Decode it!
            let inst = u32::from_le_bytes(*mem);

            // Get the opcode for the instruction
            let opcode = inst & 0b1111111;

            // Extract the common components of the instruction
            let rd     = (inst >>  7) & 0b11111;
            let rs1    = (inst >> 15) & 0b11111;
            let rs2    = (inst >> 20) & 0b11111;
            let funct3 = (inst >> 12) & 0b111;
            let funct7 = (inst >> 25) & 0b1111111;

            match opcode {
                0b0110111 => {
                    // LUI
                    if rd != 0 {
                        let imm = inst & !0xfff;
                        self.asm.load_imm(Reg::A, imm);
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0010111 => {
                    // AUIPC
                    if rd != 0 {
                        let imm = inst & !0xfff;
                        self.asm.load_imm(Reg::A, pc.wrapping_add(imm));
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b1101111 => {
                    // JAL

                    // Compute the immediate offset
                    // This is in the format `imm[20|10:1|11|19:12]`
                    let imm_31_20 = ((inst & (1 << 31)) as i32) >> (31 - 20);
                    let imm_19_12 = inst & 0b11111111000000000000;
                    let imm_11    = (inst >> (20 - 11)) & (1 << 11);
                    let imm_10_1  = (inst >> (21 -  1)) & 0b11111111110;

                    // Construct the actual immediate
                    let imm = imm_31_20 as u32 | imm_19_12 | imm_11 | imm_10_1;

                    // Compute the branch target
                    let target = pc.wrapping_add(imm);

                    if rd != 0 {
                        // Store the address of the next instruction into rd
                        self.asm.load_imm(Reg::A, pc.wrapping_add(4));
                        self.asm.write_reg(rd, Reg::A);
                    }

                    // Branch to the target
                    self.asm.load_imm(Reg::A, target);
                    self.asm.branch_a();
                }
                0b1100111 if funct3 == 0 => {
                    // JALR

                    // Get immediate
                    let imm = (inst as i32) >> 20;

                    if rd != 0 {
                        // Store the address of the next instruction into rd
                        self.asm.load_imm(Reg::A, pc.wrapping_add(4));
                        self.asm.write_reg(rd, Reg::A);
                    }

                    // Compute the branch target and branch to it
                    self.asm.read_reg(Reg::A, rs1);
                    self.asm.load_imm(Reg::B, imm as u32);
                    self.asm.add_a_b();
                    self.asm.branch_a();
                }
                0b1100011 if matches!(funct3, 0b000 | 0b001 | 0b100 | 0b101 |
                                              0b110 | 0b111) => {
                    // Conditional branches

                    // Extract immediate components
                    let imm_12   = ((inst & (1 << 31)) as i32) >> (31 - 12);
                    let imm_10_5 = (inst >> (25 - 5)) & 0b11111100000;
                    let imm_4_1  = (inst >> (8 - 1)) & 0b11110;
                    let imm_11   = (inst << (11 - 7)) & (1 << 11);

                    // Construct the immediate
                    let imm = imm_12 as u32 | imm_11 | imm_10_5 | imm_4_1;

                    // Compute true target and false target
                    let ttgt = pc.wrapping_add(imm);
                    let ftgt = pc.wrapping_add(4);

                    // Load conditional inputs
                    self.asm.read_reg(Reg::A, rs1);
                    self.asm.read_reg(Reg::B, rs2);

                    // Determine the condition we need to use
                    let (cond, ttgt, ftgt) = match funct3 {
                        // BEQ
                        0b000 => (Condition::Eq, ttgt, ftgt),

                        // BNE
                        0b001 => (Condition::Eq, ftgt, ttgt),

                        // BLT
                        0b100 => (Condition::Lt, ttgt, ftgt),

                        // BGE
                        0b101 => (Condition::Lt, ftgt, ttgt),

                        // BLTU
                        0b110 => (Condition::Ltu, ttgt, ftgt),

                        // BGEU
                        0b111 => (Condition::Ltu, ftgt, ttgt),

                        _ => unreachable!(),
                    };

                    // Perform the branch
                    self.asm.bcond_a_b(cond, ttgt, ftgt);
                }
                0b0000011 if matches!(funct3, 0b000 | 0b001 | 0b010 | 0b100 |
                                              0b101) => {
                    // Loads

                    // Get immediate
                    let imm = (inst as i32) >> 20;

                    // Compute address to load
                    self.asm.read_reg(Reg::A, rs1);
                    self.asm.load_imm(Reg::B, imm as u32);
                    self.asm.add_a_b();

                    match funct3 {
                        // LB
                        0b000 => {
                            self.asm.load_u8_a(pc);
                            self.asm.sex_u8_a();
                        }

                        // LW
                        0b001 => {
                            self.asm.load_u16_a(pc);
                            self.asm.sex_u16_a();
                        }

                        // LW
                        0b010 => self.asm.load_u32_a(pc),

                        // LBU
                        0b100 => self.asm.load_u8_a(pc),

                        // LHU
                        0b101 => self.asm.load_u16_a(pc),

                        _     => unreachable!(),
                    }

                    if rd != 0 {
                        // Update destination register
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0100011 if matches!(funct3, 0b000 | 0b001 | 0b010) => {
                    // Stores
                    
                    // Get imm components
                    let imm_11_5 = ((inst as i32) >> (25 - 5)) & !0b11111;
                    let imm_4_0  = (inst >> 7) & 0b11111;

                    // Get immediate
                    let imm = imm_11_5 as u32 | imm_4_0;
                    
                    // Compute address to write to
                    self.asm.read_reg(Reg::A, rs1);
                    self.asm.load_imm(Reg::B, imm as u32);
                    self.asm.add_a_b();

                    // Load value to write
                    self.asm.read_reg(Reg::B, rs2);

                    match funct3 {
                        // SB
                        0b000 => self.asm.store_u8_a_b(pc),

                        // SH
                        0b001 => self.asm.store_u16_a_b(pc),

                        // SW
                        0b010 => self.asm.store_u32_a_b(pc),

                        _ => unreachable!(),
                    }
                }
                0b0010011 if matches!(funct3, 0b000 | 0b010 | 0b011 | 0b100 |
                                              0b110 | 0b111) => {
                    // Immediate operations
                   
                    if rd != 0 {
                        // Get the immediate
                        let imm = ((inst as i32) >> 20) as u32;

                        // Load pseudo-registers
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.load_imm(Reg::B, imm);

                        match funct3 {
                            // ADDI
                            0b000 => self.asm.add_a_b(),

                            // SLTI
                            0b010 => self.asm.slt_a_b(),
                            
                            // SLTIU
                            0b011 => self.asm.sltu_a_b(),

                            // XORI
                            0b100 => self.asm.xor_a_b(),
                            
                            // ORI
                            0b110 => self.asm.or_a_b(),

                            // ANDI
                            0b111 => self.asm.and_a_b(),

                            _ => unreachable!(),
                        }

                        // Store the result into RD
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0010011 if funct7 == 0b0000000 && funct3 == 0b001 => {
                    // SLLI
                    if rd != 0 {
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.load_imm(Reg::B, (inst >> 20) & 0b11111);
                        self.asm.shl_a_b();
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0010011 if funct7 == 0b0000000 && funct3 == 0b101 => {
                    // SRLI
                    if rd != 0 {
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.load_imm(Reg::B, (inst >> 20) & 0b11111);
                        self.asm.shr_a_b();
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0010011 if funct7 == 0b0100000 && funct3 == 0b101 => {
                    // SRAI
                    if rd != 0 {
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.load_imm(Reg::B, (inst >> 20) & 0b11111);
                        self.asm.sar_a_b();
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0110011 if funct7 == 0b0000000 && funct3 == 0b000 => {
                    // ADD
                    if rd != 0 {
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.read_reg(Reg::B, rs2);
                        self.asm.add_a_b();
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0110011 if funct7 == 0b0100000 && funct3 == 0b000 => {
                    // SUB
                    if rd != 0 {
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.read_reg(Reg::B, rs2);
                        self.asm.sub_a_b();
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0110011 if funct7 == 0b0000000 && funct3 == 0b001 => {
                    // SLL
                    if rd != 0 {
                        // Mask the shift amount
                        self.asm.read_reg(Reg::A, rs2);
                        self.asm.load_imm(Reg::B, 0b11111);
                        self.asm.and_a_b();
                        self.asm.swap_a_b();

                        // Perform the shift
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.shl_a_b();
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0110011 if funct7 == 0b0000000 && funct3 == 0b010 => {
                    // SLT
                    if rd != 0 {
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.read_reg(Reg::B, rs2);
                        self.asm.slt_a_b();
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0110011 if funct7 == 0b0000000 && funct3 == 0b011 => {
                    // SLTU
                    if rd != 0 {
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.read_reg(Reg::B, rs2);
                        self.asm.sltu_a_b();
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0110011 if funct7 == 0b0000000 && funct3 == 0b100 => {
                    // XOR
                    if rd != 0 {
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.read_reg(Reg::B, rs2);
                        self.asm.xor_a_b();
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0110011 if funct7 == 0b0000000 && funct3 == 0b101 => {
                    // SRL
                    if rd != 0 {
                        // Mask the shift amount
                        self.asm.read_reg(Reg::A, rs2);
                        self.asm.load_imm(Reg::B, 0b11111);
                        self.asm.and_a_b();
                        self.asm.swap_a_b();

                        // Perform the shift
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.shr_a_b();
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0110011 if funct7 == 0b0100000 && funct3 == 0b101 => {
                    // SRA
                    if rd != 0 {
                        // Mask the shift amount
                        self.asm.read_reg(Reg::A, rs2);
                        self.asm.load_imm(Reg::B, 0b11111);
                        self.asm.and_a_b();
                        self.asm.swap_a_b();

                        // Perform the shift
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.sar_a_b();
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0110011 if funct7 == 0b0000000 && funct3 == 0b110 => {
                    // OR
                    if rd != 0 {
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.read_reg(Reg::B, rs2);
                        self.asm.or_a_b();
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0110011 if funct7 == 0b0000000 && funct3 == 0b111 => {
                    // AND
                    if rd != 0 {
                        self.asm.read_reg(Reg::A, rs1);
                        self.asm.read_reg(Reg::B, rs2);
                        self.asm.and_a_b();
                        self.asm.write_reg(rd, Reg::A);
                    }
                }
                0b0001111 if funct3 == 0b000 => {
                    // FENCE / PAUSE, do nothing
                }
                0b1110011 if inst == 0b00000000000000000000000001110011 => {
                    // ECALL
                }
                0b1110011 if inst == 0b00000000000100000000000001110011 => {
                    // EBREAK
                }
                _ => {
                    // Invalid opcode
                    self.asm.load_imm(Reg::A,
                        ExitStatus::InvalidOpcode as u32);
                    self.asm.load_imm(Reg::B, pc);
                    self.asm.ret();
                }
            }
        }

        let entry = self.jit_table[(self.regs[32] - BASE) as usize / 4];
        unsafe {
            self.asm.finalize();
            println!("{:#x?}",
                self.asm.enter_jit(entry,
                    &mut self.regs,
                    &mut self.memory,
                    &mut self.perms,
                    &self.jit_table));
        }

        Ok(())
    }
}

fn main() -> Result<()> {
    // Create the VM
    const BASE:  u32   = 0x10000;
    const SIZE:  usize = 128 * 1024;
    const INSTS: usize = SIZE / 4;

    let mut vm = Vm::<
        x86asm::AsmStream<BASE, SIZE, INSTS>, BASE, SIZE, INSTS
    >::from_felf("../../x509-parser/moose.felf")?;

    // JIT the VM
    vm.jit()?;

    Ok(())
}

