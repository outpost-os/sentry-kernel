
#include <sentry/arch/asm-cortex-m/semihosting.h>

#define SYS_OPEN        0x01
#define SYS_CLOSE       0x02
#define SYS_WRITEC      0x03
#define SYS_WRITE0      0x04
#define SYS_WRITE       0x05
#define SYS_READ        0x06
#define SYS_READC       0x07
#define SYS_ISERROR     0x08
#define SYS_ISTTY       0x09
#define SYS_SEEK        0x0A
#define SYS_FLEN        0x0C
#define SYS_TMPNAME     0x0D
#define SYS_REMOVE      0x0E
#define SYS_RENAME      0x0F
#define SYS_CLOCK       0x10
#define SYS_TIME        0x11
#define SYS_SYSTEM      0x12
#define SYS_ERRNO       0x13
#define SYS_GET_CMDLINE 0x15
#define SYS_HEAPINFO    0x16
#define SYS_EXIT        0x18
#define SYS_ELAPSED     0x30
#define SYS_TICKFREQ    0x31

/**
 * @brief Make a Thumb mode semihosting system call
 *
 * @param op semihosting call operation code
 * @param argv argument array
 *
 * Semihosting call is automagically catch by debugger if enable in its side.
 * In thumb mode, every time the CPU break on "0xAB" breakpoint (thumb opcode `0xbeab`)
 * debugger will fetch `r0` (op) and `r1` (argv) registers and execute the corresponding system call
 * in the host environment.
 *
 * The second automagically trick here is that arm eabi defined that the first arg is in `r0`
 * and the second in `r1`. So, there is **nothing** to do but preventing the compiler to trim
 * these away. So, this function is **never** inlined and non optimized.
 *
 * Debugger will then write `r0` with syscall return code, so, there is **nothing** (again) to do
 * but return (i.e. branching to link register).
 *
 * For all these reason, there is no need for prolog nor epilog, thus this is a naked function.
 *
 * @warning do not use this without enabling semihosting on debugger side, otherwise
 *          core will hang until reset.
 *
 * @return host executed call return code
 */
__attribute__((noinline, naked, optimize("-O0")))
static int thumb_semihosting_call(int op [[gnu::unused]], int* argv [[gnu::unused]])
{
    asm inline (
        "bkpt #0xAB     \n\t\
         bx lr          \n\t\
        ");
}

/**
 * @brief open a file on host operating system
 *
 * @param filename pointer to null-terminated string containing file or device name
 * @param mode file opening mode
 * @param length filename string length (w/o null character)
 *
 * @return -1 on error, file handle on success
 */
int arm_semihosting_open(const char* filename, int mode, int length)
{
    int argv[3];

    argv[0] = (int)filename;
    argv[1] = mode;
    argv[2] = length;

    return thumb_semihosting_call(SYS_OPEN, argv);
}

int arm_semihosting_close(int file)
{
    int argv[1];

    argv[0] = file;

    return thumb_semihosting_call(SYS_CLOSE, argv);
}

int arm_semihosting_writec(char c)
{
    return thumb_semihosting_call(SYS_WRITEC, (int *)&c);
}

int arm_semihosting_write0(const char* s)
{
    return thumb_semihosting_call(SYS_WRITE0, (int *)s);
}

int arm_semihosting_write(int file, const char* buffer, int length)
{
    int argv[3];

    argv[0] = file;
    argv[1] = (int)buffer;
    argv[2] = length;

    return thumb_semihosting_call(SYS_WRITE, argv);
}
