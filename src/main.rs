//! An extremely basic RISC-V (rv32i) emulator

#![feature(array_chunks)]

mod vm;
pub mod x86asm;

pub use vm::{Vm, Register, VmExit, Result, Error};

fn main() -> Result<()> {
    // Create the VM
    const BASE:    u32   = 0x10000;
    const SIZE:    usize = 256 * 1024;
    const INSTS:   usize = SIZE / 4;
    const STACKSZ: u32   = 32 * 1024;
    const HEAPSZ:  u32   = 32 * 1024;

    // Create a VM from the example target
    let mut vm = Vm::<
        x86asm::AsmStream<BASE, SIZE, INSTS>,
        BASE, SIZE, INSTS, STACKSZ, HEAPSZ
    >::from_felf("example_target/example.felf")?;

    // JIT the VM
    vm.jit()?;

    // Execute VM
    'vm_loop: loop {
        let exit = vm.run();
        match exit {
            VmExit::Coverage => {},
            VmExit::Ecall => {
                // Syscall
                let number = vm.reg(Register::A7);

                match number {
                    100 => {
                        // Write byte in A0
                        let byte = vm.reg(Register::A0) as u8;
                        print!("{}", byte as char);
                    }
                    101 => {
                        // Exit
                        let code = vm.reg(Register::A0) as i32;
                        println!("Exited with: {}", code);
                        break 'vm_loop;
                    }
                    102 => {
                        // Sbrk
                        let ret = vm.sbrk(vm.reg(Register::A0) as i32);
                        if let Some(ret) = ret {
                            vm.set_reg(Register::A0, ret);
                        } else {
                            // Failed to allocate
                            vm.set_reg(Register::A0, !0);
                        }
                    }
                    _ => panic!("Unhandled syscall {}", number),
                }
            }
            _ => {
                vm.dump_regs();
                panic!("Unhandled vmexit {:x?}", exit);
            }
        }
    }

    Ok(())
}

