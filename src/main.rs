//! An extremely basic RISC-V (rv32i) emulator

#![feature(array_chunks, scoped_threads)]

mod vm;
pub mod x86asm;

pub use vm::{Vm, Register, VmExit, Result, Error};

use std::time::{Duration, Instant};
use std::sync::atomic::{AtomicU64, Ordering};

// VM properties we're going to use
const BASE:    u32   = 0x10000;
const SIZE:    usize = 256 * 1024;
const INSTS:   usize = SIZE / 4;
const STACKSZ: u32   = 32 * 1024;
const HEAPSZ:  u32   = 32 * 1024;
const DIRTY:   usize = SIZE / (256 * 8);

/// Re-type a VM with our specific properties
type OurVm = Vm::<
    x86asm::AsmStream<BASE, SIZE, INSTS, DIRTY>,
    BASE, SIZE, INSTS, STACKSZ, HEAPSZ, DIRTY
>;

/// Simple wrapper to get the TSC
fn rdtsc() -> u64 {
    unsafe { std::arch::x86_64::_rdtsc() }
}

/// Stats to track what's going on with our VMs!
#[derive(Default)]
struct Statistics {
    /// Number of fuzz cases executed
    cases: AtomicU64,

    /// Cycles restoring the VM state
    cycles_reset: AtomicU64,

    /// Cycles running the VM
    cycles_run: AtomicU64,

    /// Cycles handling VM exits
    cycles_vmexit: AtomicU64,
}

/// Worker thread for fuzz workers
fn worker(orig_vm: &OurVm, mut vm: OurVm, stats: &Statistics) {
    // Time of the last global statistics update
    let mut last_report = rdtsc();

    // Thread-local statistics we merge only when needed
    let mut cases_execed  = 0;
    let mut cycles_reset  = 0; // Cycles restoring the VM state
    let mut cycles_run    = 0; // Cycles running the VM
    let mut cycles_vmexit = 0; // Cycles handling VM exits/syscalls

    loop {
        // Reset VM state to the state of `orig_vm`
        let it = rdtsc();
        vm.reset_to(orig_vm);
        cycles_reset += rdtsc() - it;

        // Loop while handling vmexits
        let mut execute = true;
        while execute {
            // Execute the VM!
            let it = rdtsc();
            let exit = vm.run();
            cycles_run += rdtsc() - it;

            // Handle vmexits
            let it = rdtsc();
            match exit {
                VmExit::Coverage => {},
                VmExit::Ecall => {
                    // Syscall
                    let number = vm.reg(Register::A7);

                    match number {
                        100 => {
                            // Write byte in A0
                            let byte = vm.reg(Register::A0) as u8;
                            //print!("{}", byte as char);
                        }
                        101 => {
                            // Exit
                            let code = vm.reg(Register::A0) as i32;
                            //println!("Exited with: {}", code);

                            // Stop execution
                            execute = false;
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
            cycles_vmexit += rdtsc() - it;
        }

        // Update number of cases
        cases_execed += 1;

        // Only update statistics globally every 100M cycles
        // Divide your CPUs clock rate by this to get the approximate update
        // interval. This is to prevent cache thrashing between cores
        if rdtsc() - last_report > 100_000_000 {
            // Update stats
            stats.cases.fetch_add(cases_execed, Ordering::Relaxed);
            stats.cycles_reset.fetch_add(cycles_reset, Ordering::Relaxed);
            stats.cycles_run.fetch_add(cycles_run, Ordering::Relaxed);
            stats.cycles_vmexit.fetch_add(cycles_vmexit, Ordering::Relaxed);
            cases_execed  = 0;
            cycles_reset  = 0;
            cycles_run    = 0;
            cycles_vmexit = 0;

            // Save the current time
            last_report = rdtsc();
        }
    }
}

fn main() -> Result<()> {
    // Create the VM

    // Create a VM from the example target
    let mut orig_vm = OurVm::from_felf("example_target/example.felf")?;

    // JIT the VM
    orig_vm.jit()?;

    // Create statistics structure
    let stats = Statistics::default();

    // Fork the VM for each thread
    std::thread::scope(|s| {
        for _ in 0..8 {
            let vm = orig_vm.clone();
            s.spawn(|_| {
                worker(&orig_vm, vm, &stats);
            });
        }

        // Start a timer and print stats!
        let it = Instant::now();
        loop {
            // Pause a bit
            std::thread::sleep(Duration::from_millis(100));

            // Print stats
            let uptime = it.elapsed().as_secs_f64();
            let cases  = stats.cases.load(Ordering::Relaxed);
            let crst   = stats.cycles_reset.load(Ordering::Relaxed);
            let crun   = stats.cycles_run.load(Ordering::Relaxed);
            let cvme   = stats.cycles_vmexit.load(Ordering::Relaxed);
            let ctot   = crst + crun + cvme;
            let fcps   = cases as f64 / uptime;
            let prst   = crst as f64 / ctot as f64;
            let prun   = crun as f64 / ctot as f64;
            let pvme   = cvme as f64 / ctot as f64;
            println!("[{uptime:12.6}] cases {cases:10} | fcps {fcps:10.1} | \
                reset {prst:5.3} | run {prun:5.3} | vmexit {pvme:5.3}");
        }
    });

    Ok(())
}

