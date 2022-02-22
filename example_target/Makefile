all:
	riscv32-elf-gcc -ggdb -O2 -specs=nosys.specs example.c -o example
	elfloader --perms example example.felf

