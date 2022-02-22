//! An extremely basic RISC-V (rv32i) emulator

#![feature(array_chunks)]

mod vm;
pub mod x86asm;

pub use vm::{Vm, Register, VmExit, Result, Error};

