#include <stdio.h>

int
main(int argc, char *argv[]) {
    // Crash!
    *(volatile int*)0x13371330 = argv;

    return 0;
}

