all: x86_64

x86_64: \
	asm_helpers/x86_64/branch.bin  \
	asm_helpers/x86_64/load8.bin   \
	asm_helpers/x86_64/load16.bin  \
	asm_helpers/x86_64/load32.bin  \
	asm_helpers/x86_64/store8.bin  \
	asm_helpers/x86_64/store16.bin \
	asm_helpers/x86_64/store32.bin \

asm_helpers/x86_64/branch.bin: asm_helpers/x86_64/branch.asm \
		asm_helpers/x86_64/consts.inc
	nasm -f bin asm_helpers/x86_64/branch.asm \
		-p asm_helpers/x86_64/consts.inc -o asm_helpers/x86_64/branch.bin

asm_helpers/x86_64/load8.bin: asm_helpers/x86_64/memory.asm \
		asm_helpers/x86_64/consts.inc
	nasm -f bin -DOPSIZE=8 -DSTORE=0 asm_helpers/x86_64/memory.asm \
		-p asm_helpers/x86_64/consts.inc -o asm_helpers/x86_64/load8.bin

asm_helpers/x86_64/load16.bin: asm_helpers/x86_64/memory.asm \
		asm_helpers/x86_64/consts.inc
	nasm -f bin -DOPSIZE=16 -DSTORE=0 asm_helpers/x86_64/memory.asm \
		-p asm_helpers/x86_64/consts.inc -o asm_helpers/x86_64/load16.bin

asm_helpers/x86_64/load32.bin: asm_helpers/x86_64/memory.asm \
		asm_helpers/x86_64/consts.inc
	nasm -f bin -DOPSIZE=32 -DSTORE=0 asm_helpers/x86_64/memory.asm \
		-p asm_helpers/x86_64/consts.inc -o asm_helpers/x86_64/load32.bin

asm_helpers/x86_64/store8.bin: asm_helpers/x86_64/memory.asm \
		asm_helpers/x86_64/consts.inc
	nasm -f bin -DOPSIZE=8 -DSTORE=1 asm_helpers/x86_64/memory.asm \
		-p asm_helpers/x86_64/consts.inc -o asm_helpers/x86_64/store8.bin

asm_helpers/x86_64/store16.bin: asm_helpers/x86_64/memory.asm \
		asm_helpers/x86_64/consts.inc
	nasm -f bin -DOPSIZE=16 -DSTORE=1 asm_helpers/x86_64/memory.asm \
		-p asm_helpers/x86_64/consts.inc -o asm_helpers/x86_64/store16.bin

asm_helpers/x86_64/store32.bin: asm_helpers/x86_64/memory.asm \
		asm_helpers/x86_64/consts.inc
	nasm -f bin -DOPSIZE=32 -DSTORE=1 asm_helpers/x86_64/memory.asm \
		-p asm_helpers/x86_64/consts.inc -o asm_helpers/x86_64/store32.bin

