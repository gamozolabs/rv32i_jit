all:
	riscv32-elf-gcc -ggdb -O0 -Wall -specs=nosys.specs \
		main.c rtos.c x509-parser.c -o x509-parser
	elfloader --perms x509-parser x509-parser.felf

clean:
	rm -f x509-parser x509-parser.felf

