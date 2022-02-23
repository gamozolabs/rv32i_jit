/*
 *  Copyright (C) 2019 - This file is part of x509-parser project
 *
 *  Author:
 *      Arnaud EBALARD <arnaud.ebalard@ssi.gouv.fr>
 *
 *  This software is licensed under a dual GPLv2/BSD license. See
 *  LICENSE file at the root folder of the project.
 */

#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include "x509-parser.h"
#include <unistd.h>

u8 fuzz_input[128 * 1024] = { 0 };
u16 fuzz_input_len = 0;

long syscall(long num, long arg0, long arg1);

int main(int argc, char *argv[])
{
	cert_parsing_ctx ctx;

    // Report the addresses of the fuzz input buffers
    syscall(103, (long)fuzz_input, (long)&fuzz_input_len);

	return parse_x509_cert(&ctx, fuzz_input, fuzz_input_len);
}

