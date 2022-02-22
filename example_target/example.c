#include <stdio.h>

int
main(void) {
    // Crash!
    *(volatile int*)0x13371330 = 0;

    return 0;
}

