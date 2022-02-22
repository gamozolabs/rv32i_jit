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

# Example

The current example in the tree (as of `0521ad1`) demonstrates spinning up
VMs on multiple cores, resetting them to an original state, and executing them.
The example program is a simple Hello World C application and on my machine
I get approximately ~107k hello worlds per second on a single 2.1 GHz core,
and on my 192 thread (96 core) 2.3 GHz server I get approximately 8.6 million
hello worlds per second. Near-linear scaling while gahtering code coverage
and the like.

