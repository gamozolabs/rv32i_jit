//! An extremely basic RISC-V (rv32i) emulator

#![feature(array_chunks, scoped_threads)]

mod vm;
pub mod x86asm;

pub use vm::{Vm, Register, VmExit, Result, Error};

// VM properties we're going to use
const BASE:    u32   = 0x10000;
const SIZE:    usize = 256 * 1024;
const INSTS:   usize = SIZE / 4;
const STACKSZ: u32   = 32 * 1024;
const HEAPSZ:  u32   = 32 * 1024;

/// Re-type a VM with our specific properties
type OurVm = Vm::<
    x86asm::AsmStream<BASE, SIZE, INSTS>,
    BASE, SIZE, INSTS, STACKSZ, HEAPSZ
>;

/// Worker thread for fuzz workers
fn worker(orig_vm: &OurVm, mut vm: OurVm) {
    loop {
        // Reset VM state to the state of `orig_vm`
        vm.reset_to(orig_vm);

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
    }
}

fn main() -> Result<()> {
    // Create the VM

    // Create a VM from the example target
    let mut orig_vm = OurVm::from_felf("example_target/example.felf")?;

    // JIT the VM
    orig_vm.jit()?;

    // Fork the VM for each thread
    std::thread::scope(|s| {
        for _ in 0..16 {
            let vm = orig_vm.clone();
            s.spawn(|_| {
                worker(&orig_vm, vm);
            });
        }
    });

    Ok(())
}

