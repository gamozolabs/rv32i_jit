all:
	riscv32-elf-gcc -ggdb -O2 -Wall -specs=nosys.specs \
		example.c rtos.c -o example
	elfloader --perms example example.felf

