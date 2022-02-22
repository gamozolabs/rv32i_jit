#include <errno.h>
#include <sys/stat.h>
#include <sys/times.h>

// Expose errno
#undef errno
extern int errno;

long syscall(long num, long arg0) {
    register long a0 asm("a0") = arg0;
    register long a7 asm("a7") = num;
    asm volatile ("ecall" : "+r"(a0) : "r"(a7));
    return a0;
}

void write_byte(char byte) {
    syscall(100, (long)byte);
}

// Exit a program without cleaning up files. If your system doesn’t provide
// this, it is best to avoid linking with subroutines that require it (exit,
// system).
__attribute__((noreturn))
void _exit(int code) {
    for( ; ; ) {
        // Exit!
        syscall(101, code);
    }
}

// Close a file. Minimal implementation
int _close(int file) {
    return -1;
}

// A pointer to a list of environment variables and their values. For a minimal
// environment, this empty list is adequate
char *__env[1] = { 0 };
char **environ = __env;

// Transfer control to a new process. Minimal implementation (for a system
// without processes)
int _execve(char *name, char **argv, char **env) {
    errno = ENOMEM;
    return -1;
}

// Create a new process. Minimal implementation (for a system without
// processes)
int _fork(void) {
    errno = EAGAIN;
    return -1;
}

// Status of an open file. For consistency with other minimal implementations
// in these examples, all files are regarded as character special devices. The
// sys/stat.h header file required is distributed in the include subdirectory
// for this C library.
int _fstat(int file, struct stat *st) {
  st->st_mode = S_IFCHR;
  return 0;
}

// Process-ID; this is sometimes used to generate strings unlikely to conflict
// with other processes. Minimal implementation, for a system without
// processes
int _getpid(void) {
    return 1;
}

// Query whether output stream is a terminal. For consistency with the other
// minimal implementations, which only support output to stdout, this minimal
// implementation is suggested
int _isatty(int file) {
    return 1;
}

// Send a signal. Minimal implementation
int _kill(int pid, int sig) {
    errno = EINVAL;
    return -1;
}

// Establish a new name for an existing file. Minimal implementation
int _link(char *old, char *new) {
    errno = EMLINK;
    return -1;
}

// Set position in a file. Minimal implementation
int _lseek(int file, int ptr, int dir) {
    return 0;
}

// Open a file. Minimal implementation
int _open(const char *name, int flags, int mode) {
    return -1;
}

// Read from a file. Minimal implementation
int _read(int file, char *ptr, int len) {
    return 0;
}

// Increase program data space
caddr_t _sbrk(int incr) {
    return (caddr_t)syscall(102, incr);
}

// Status of a file (by name). Minimal implementation
int _stat(char *file, struct stat *st) {
    st->st_mode = S_IFCHR;
    return 0;
}

// Timing information for current process. Minimal implementation
int _times(struct tms *buf) {
    return -1;
}

// Remove a file’s directory entry. Minimal implementation
int _unlink(char *name) {
    errno = ENOENT;
    return -1;
}

// Wait for a child process. Minimal implementation
int _wait(int *status) {
    errno = ECHILD;
    return -1;
}

// Write to a file. libc subroutines will use this system routine for output to
// all files, including stdout—so if you need to generate any output, for
// example to a serial port for debugging, you should make your minimal write
// capable of doing this. The following minimal implementation is an incomplete
// example; it relies on a outbyte subroutine (not shown; typically, you must
// write this in assembler from examples provided by your hardware
// manufacturer) to actually perform the output
int _write(int file, char *ptr, int len) {
    for(int ii = 0; ii < len; ii++) {
        write_byte(*ptr++);
    }

    return len;
}

