//! RISC-V lifter and VM

use std::path::Path;

/// Wrapper around [`Error`]
pub type Result<T> = std::result::Result<T, Error>;

/// Error types for this crate
#[derive(Debug)]
pub enum Error {
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

    /// Failed to find a location to allocate the stack
    AllocStack,

    /// Failed to find a location to allocate the heap
    AllocHeap,

    /// Dirty bits are expected to be at a ratio of 1:256 compared to memory
    /// size
    InvalidDirtyCount,
}

/// A label which references an assembly location
#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
pub struct Label(pub usize);

/// Registers for the pseudo-architecture we use for the assembler
pub enum Reg {
    /// The A register!
    A,

    /// The B register!
    B,
}

/// Condition codes for conditional branches
pub enum Condition {
    /// Equal
    Eq,

    /// Signed less than
    Lt,

    /// Unsigned less than
    Ltu,
}

/// A trait defining the basic operations of an assembler
pub trait Assembler<const BASE: u32, const MEMSIZE: usize,
                    const INSTRS: usize, const DIRTY: usize>: Default + Clone {
    /// Create a label for the current location in the assembly stream
    fn label(&mut self) -> Label;

    /// Copy the JIT into executable memory
    fn finalize(&mut self);

    /// Start executing the JIT at `label` and return the pseudo-architecture
    /// A and B registers
    ///
    /// Upon return A should be the `ExitStatus` code that caused the exit
    /// B should be further information for the exit status
    ///
    /// Exiting the JIT requires that you correctly update `regs[32]` with
    /// the PC value which reflects where the exit occurred
    ///
    /// ExecFault     - PC should be the instruction that was attempted to exec
    /// ReadFault     - PC should be the address of the faulting instruction
    /// WriteFault    - PC should be the address of the faulting instruction
    /// InvalidOpcode - PC should be the address of the invalid instruction
    /// Ecall         - PC should be the address of the following instruction
    /// Ebreak        - PC should be the address of the following instruction
    unsafe fn enter_jit(
        &self,
        label:     Label,
        regs:      &mut [u32; 33],
        mem:       &mut [u8; MEMSIZE],
        perms:     &mut [u8; MEMSIZE],
        dirty:     &mut [u8; DIRTY],
        jit_table: &[Label; INSTRS],
    ) -> (u32, u32);

    /// Emit an operation which will cause a `Coverage` vmexit, but only
    /// the first time it is hit per occurance of `coverage_oneshot`
    /// It's okay if this fires a coverage event for the same PC multiple
    /// times (eg. while waiting for caches to update), but it should attempt
    /// to self-silence as soon as possible
    fn coverage_oneshot(&mut self, pc: u32);

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

/// A guest virtual machine
#[derive(Clone)]
pub struct Vm<ASM: Assembler<BASE, MEMSIZE, INSTRS, DIRTY>,
          const BASE: u32, const MEMSIZE: usize, const INSTRS: usize,
          const STACK_SIZE: u32, const HEAP_SIZE: u32, const DIRTY: usize> {
    /// VM GPR register state + PC
    regs: [u32; 33],

    /// Backing memory for the VM
    memory: Box<[u8; MEMSIZE]>,

    /// Backing permissions for the VM
    perms: Box<[u8; MEMSIZE]>,

    /// Dirty bit storage
    /// This is a bitmap containing which bytes of memory have been written
    /// to since the last time this was cleared
    dirty: Box<[u8; DIRTY]>,

    /// Lookup table from all possible instructions to JIT labels
    jit_table: Box<[Label; INSTRS]>,

    /// Current heap pointer
    heap_cur: u32,

    /// End of the heap
    heap_end: u32,

    /// Assembler which holds the JITted code
    asm: ASM,
}

/// Permission bit flags
#[repr(u8)]
pub enum Perm {
    /// Execute permissions
    Exec = 0x01,

    /// Write permissions
    Write = 0x02,

    /// Read permissions
    Read = 0x04,
}

/// JIT exit statuses
#[repr(u32)]
pub enum ExitStatus {
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

    /// An `ecall` instruction was executed, PC will point to the following
    /// instruction for re-entry
    Ecall = 0xdead0004,

    /// An `ebreak` instruction was executed, PC will point to the following
    /// instruction for re-entry
    Ebreak = 0xdead0005,

    /// An instruction has been hit for the first time
    Coverage = 0xdead0006,
}

/// RISCV register names
#[derive(Clone, Copy, Debug)]
#[repr(u8)]
pub enum Register {
    Zero, Ra, Sp, Gp, Tp, T0, T1, T2, Fp, S1, A0, A1, A2, A3, A4, A5, A6, A7,
    S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, T3, T4, T5, T6, PC,
}

/// Rust-typed VM exits
#[derive(Debug, Clone, Copy)]
pub enum VmExit {
    /// Attempted to execute an instruction which is not executable
    ExecFault { addr: u32 },

    /// Attempted to execute an invalid instruction
    InvalidOpcode,

    /// Attempted to read memory which is not readable
    ReadFault { addr: u32 },

    /// Attempted to write to memory which is not writable
    WriteFault { addr: u32 },

    /// Guest executed an `ecall` instruction
    Ecall,

    /// Guest executed an `ebreak` instruction
    Ebreak,

    /// New code was executed for the first time
    Coverage,
}

impl<ASM: Assembler<BASE, MEMSIZE, INSTRS, DIRTY>,
     const BASE: u32, const MEMSIZE: usize, const INSTRS: usize,
     const STACK_SIZE: u32, const HEAP_SIZE: u32, const DIRTY: usize>
        Vm<ASM, BASE, MEMSIZE, INSTRS, STACK_SIZE, HEAP_SIZE, DIRTY> {
    /// Create a VM from a FELF
    pub fn from_felf(felf: impl AsRef<Path>) -> Result<Self> {
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

        // Currently we expect 256-byte granularity for dirty bits
        if DIRTY == 0 || DIRTY != MEMSIZE / (256 * 8) {
            return Err(Error::InvalidDirtyCount);
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

        // Update starting PC to be the start location for the binary
        regs[32] = entry;

        // Allocate dirty bits
        let dirty: Box<[u8; DIRTY]> =
            vec![0; DIRTY].into_boxed_slice().try_into().unwrap();

        // Return the clean VM state
        let mut ret = Self {
            memory:   raw_memory,
            perms:    raw_perms,
            asm:      ASM::default(),
            heap_cur: 0,
            heap_end: 0,
            jit_table,
            dirty,
            regs,
        };

        // Allocate a stack
        let stack = ret.alloc(STACK_SIZE).ok_or(Error::AllocStack)?;

        // Compute the stack address
        //
        // Stack upon _start should be:
        // [END OF STACK]
        // [NULL pointer (end of argv)]
        // [argv...]
        // [argc: u32]
        ret.regs[2] = stack + STACK_SIZE - 8;

        // Zero out argc and put a NULL terminator at argv[0]
        ret.memory[(ret.regs[2] - BASE) as usize..][..8]
            .copy_from_slice(&[0u8; 8]);

        // Allocate a heap
        let heap = ret.alloc(HEAP_SIZE).ok_or(Error::AllocHeap)?;
        ret.heap_cur = heap;
        ret.heap_end = heap + HEAP_SIZE;

        Ok(ret)
    }

    /// Update `self` to be in the same state as `other`
    pub fn reset_to(&mut self, other: &Self) {
        // Reset register state
        self.regs.copy_from_slice(&other.regs);

        for (ii, byte) in self.dirty.iter_mut().enumerate() {
            // Skip non-dirty bytes
            if *byte == 0 { continue; }

            // Replace the dirty byte with zero, indicating it's no longer
            // dirty, and take it into our own ownership
            let mut tmp = 0u8;
            std::mem::swap(&mut tmp, byte);

            for bit in 0..8 {
                if tmp & (1 << bit) != 0 {
                    // Determine the offset of the dirtied memory
                    let offset = (ii * 256 * 8) + bit * 256;

                    // Restore memory for this region
                    self.memory[offset..offset + 256].copy_from_slice(
                        &other.memory[offset..offset + 256]);
                    self.perms[offset..offset + 256].copy_from_slice(
                        &other.perms[offset..offset + 256]);
                }
            }
        }

        // Reset heap state
        self.heap_cur = other.heap_cur;
        self.heap_end = other.heap_end;
    }

    /// Update permissions for `addr` for `size` bytes to `perm`
    pub fn set_permissions(&mut self, addr: u32, size: u32, perm: u8)
            -> Option<()> {
        // Get the start and end indicies of the region to update
        let start  = addr.checked_sub(BASE)?;
        let end    = start.checked_add(size)?;
        let region = self.perms.get_mut(start as usize..end as usize)?;

        // Make sure the permission is allowed
        let is_exec = (perm & (Perm::Exec as u8)) != 0;
        if is_exec {
            // Cannot create executable memory
            return None;
        }

        // Set permissions
        region.iter_mut().for_each(|x| *x = perm);

        // Update dirty bits
        for idx in (start / 256)..(end + 255) / 256 {
            let byte = idx / 8;
            let bit  = idx % 8;
            self.dirty[byte as usize] |= 1 << bit;
        }

        Some(())
    }

    /// Find a region of bytes which are unused (permissions are 0) which is
    /// large enough to hold `size` bytes
    ///
    /// Always returns 16-byte aligned memory
    pub fn alloc(&mut self, size: u32) -> Option<u32> {
        // Attempt to find a location for the memory
        for ii in (0..self.perms.len()).step_by(16) {
            // Get a slice of memory at this address
            if let Some(slice) = self.perms[ii..].get(..size as usize){
                // If all permissions are completely unused, this is usable for
                // an allocation
                if slice.iter().all(|x| *x == 0) {
                    // Set permissions to RW for the heap
                    self.set_permissions(BASE + ii as u32, size,
                        Perm::Read as u8 | Perm::Write as u8);

                    // Found and allocated memory!
                    return Some(BASE + ii as u32);
                }
            }
        }

        // Couldn't find any memory :(
        None
    }

    /// Increase/decrease heap usage by `increase` bytes and return the
    /// previous program break location
    pub fn sbrk(&mut self, increase: i32) -> Option<u32> {
        // We don't support reducing memory right now
        if increase < 0 {
            return None;
        }

        // Get the current heap location
        let ret = self.heap_cur;

        // Update heap pointer
        self.heap_cur = ret.checked_add(increase as u32)?;

        // Make sure we're in bounds of the heap
        if self.heap_cur > self.heap_end {
            return None;
        }

        // Return old break location
        Some(ret)
    }

    /// JIT all the instructions in the VM, I guess it's not actually a JIT
    /// but a translation but too bad
    pub fn jit(&mut self) -> Result<()> {
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

            // Emit oneshot coverage logging
            self.asm.coverage_oneshot(pc);

            // If it's not executable, emit the execution fault code
            if !executable {
                // Update PC
                self.asm.load_imm(Reg::A, pc);
                self.asm.write_reg(32, Reg::A);

                self.asm.load_imm(Reg::A, ExitStatus::ExecFault as u32);
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

                        _ => unreachable!(),
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

                    // Update PC to the instruction following the call
                    self.asm.load_imm(Reg::A, pc.wrapping_add(4));
                    self.asm.write_reg(32, Reg::A);

                    // Update return status
                    self.asm.load_imm(Reg::A, ExitStatus::Ecall as u32);
                    self.asm.ret();
                }
                0b1110011 if inst == 0b00000000000100000000000001110011 => {
                    // EBREAK

                    // Update PC to the instruction following the break
                    self.asm.load_imm(Reg::A, pc.wrapping_add(4));
                    self.asm.write_reg(32, Reg::A);

                    // Update return status
                    self.asm.load_imm(Reg::A, ExitStatus::Ebreak as u32);
                    self.asm.ret();
                }
                _ => {
                    // Update PC
                    self.asm.load_imm(Reg::A, pc);
                    self.asm.write_reg(32, Reg::A);

                    // Invalid opcode
                    self.asm.load_imm(Reg::A,
                        ExitStatus::InvalidOpcode as u32);
                    self.asm.ret();
                }
            }
        }

        // Commit the JIT to RWX memory
        self.asm.finalize();

        Ok(())
    }

    /// Pretty print target register state
    pub fn dump_regs(&self) {
        println!(r#"pc   {:08x}
zero {:08x} ra {:08x} sp  {:08x} gp  {:08x} tp {:08x} t0 {:08x}
t1   {:08x} t2 {:08x} fp  {:08x} s1  {:08x} a0 {:08x} a1 {:08x}
a2   {:08x} a3 {:08x} a4  {:08x} a5  {:08x} a6 {:08x} a7 {:08x}
s2   {:08x} s3 {:08x} s4  {:08x} s5  {:08x} s6 {:08x} s7 {:08x}
s8   {:08x} s9 {:08x} s10 {:08x} s11 {:08x} t3 {:08x} t4 {:08x}
t5   {:08x} t6 {:08x}
        "#,
        self.regs[32],
        self.regs[ 0], self.regs[ 1], self.regs[ 2], self.regs[ 3],
        self.regs[ 4], self.regs[ 5], self.regs[ 6], self.regs[ 7],
        self.regs[ 8], self.regs[ 9], self.regs[10], self.regs[11],
        self.regs[12], self.regs[13], self.regs[14], self.regs[15],
        self.regs[16], self.regs[17], self.regs[18], self.regs[19],
        self.regs[20], self.regs[21], self.regs[22], self.regs[23],
        self.regs[24], self.regs[25], self.regs[26], self.regs[27],
        self.regs[28], self.regs[29], self.regs[30], self.regs[31]);
    }

    /// Get a register value
    pub fn reg(&self, reg: Register) -> u32 {
        self.regs[reg as usize]
    }

    /// Set a register value
    pub fn set_reg(&mut self, reg: Register, val: u32) {
        self.regs[reg as usize] = val;
    }

    /// Execute the VM until the next VM exit
    pub fn run(&mut self) -> VmExit {
        // Determine the entry location
        let offset = self.regs[32].checked_sub(BASE);
        let entry = offset.and_then(|x| self.jit_table.get(x as usize / 4));
        if entry.is_none() { return VmExit::ExecFault { addr: self.regs[32] } }
        let entry = *entry.unwrap();

        // Enter the JIT
        let (code, status) = unsafe {
            self.asm.enter_jit(entry,
                &mut self.regs,
                &mut self.memory,
                &mut self.perms,
                &mut self.dirty,
                &self.jit_table)
        };

        // Translate the return code
        if code == ExitStatus::ExecFault as u32 {
            VmExit::ExecFault { addr: status }
        } else if code == ExitStatus::InvalidOpcode as u32 {
            VmExit::InvalidOpcode
        } else if code == ExitStatus::ReadFault as u32 {
            VmExit::ReadFault { addr: status }
        } else if code == ExitStatus::WriteFault as u32 {
            VmExit::WriteFault { addr: status }
        } else if code == ExitStatus::Ecall as u32 {
            VmExit::Ecall
        } else if code == ExitStatus::Ebreak as u32 {
            VmExit::Ebreak
        } else if code == ExitStatus::Coverage as u32 {
            VmExit::Coverage
        } else {
            panic!("VM exited with unknown exit status {:#x} {:#x}",
                code, status);
        }
    }
}

