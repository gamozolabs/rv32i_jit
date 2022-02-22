# Summary

Hello! This is a project I wrote for preparing some data for my Bluehat IL
talk. I mainly just needed to collect code coverage and monitor fuzzers so
I wrote this little tool.

This is a RISC-V JIT for rv32i. This is designed to be easily extended and
modified, and is not designed for performance. It appears performance of this
gets approximately 1 RISC-V instruction per every 2 x86 cycles. This makes it
a pretty slow JIT, and there's a lot of expensive things (like all branches are
indirect). However, that is intentional. It reduces the amount of places you
have to hook and instrument.

This engine supports differential resetting of VMs and byte-level permissions
on all memory accesses, allowing you to implement things like ASAN on binary
targets. It also should scale linearly with cores.

Anyways, it's a really simple design and should be easy to hack on or add a
backend that isn't x86, you only have to implement a very small assembler
to get support for your architecture!

# Building apps

To build applications, you'll need a RV32i newlib toolchain. Specifically you
need to build all code with `-march=rv32i` and as soft-float, and you need
to build with `-specs=nosys.specs` as is done in the example project. This
should provide a nearly full-featured libc environment, and thus most
single-threaded basic C code should build and run in this environment. It's
up to you to define your syscalls as needed.

# Features

- Byte-level permissions (can add ASAN-level protections to binary code)
- Scales linearly with cores (nothing shared between cores or using Linux
  syscalls)
- PC-level code coverage that converges to no overhead since it stops reporting
  once hit
- Easy-to-use interface (read and write registers, handle vmexits as needed)
- Out-performs Linux by a significant margin for process startup and forking
- Simple code which is designed to be easy to hook and modify
- Differential resetting of VMs based on dirtied memory
- Easy-to-port backend for making a JIT for your desired architecture, only
  about ~300 LoC to implement a fully-featured backend

# Example

The current example in the tree (as of `0521ad1`) demonstrates spinning up
VMs on multiple cores, resetting them to an original state, and executing them.
The example program is a simple Hello World C application and on my machine
I get approximately ~107k hello worlds per second on a single 2.1 GHz core,
and on my 192 thread (96 core) 2.3 GHz server I get approximately 8.6 million
hello worlds per second. Near-linear scaling while gahtering code coverage
and the like.

```
pleb@polar ~ $ ./jit 
[    0.100064] cases    1109821 | fcps 11091081.8 | coverage    1522 | reset 0.028 | run 0.953 | vmexit 0.019
[    0.200148] cases    1748147 | fcps  8734259.0 | coverage    1522 | reset 0.029 | run 0.952 | vmexit 0.019
[    0.300216] cases    2536983 | fcps  8450525.5 | coverage    1522 | reset 0.029 | run 0.952 | vmexit 0.019
[    0.400283] cases    3293115 | fcps  8226972.7 | coverage    1522 | reset 0.029 | run 0.952 | vmexit 0.019
[    0.500350] cases    4054432 | fcps  8103192.5 | coverage    1522 | reset 0.030 | run 0.952 | vmexit 0.018
[    0.600418] cases    4851220 | fcps  8079734.0 | coverage    1522 | reset 0.030 | run 0.952 | vmexit 0.018
[    0.700485] cases    5648671 | fcps  8063940.7 | coverage    1522 | reset 0.030 | run 0.952 | vmexit 0.018
[    0.800658] cases    6490916 | fcps  8106977.7 | coverage    1522 | reset 0.031 | run 0.952 | vmexit 0.018
```

