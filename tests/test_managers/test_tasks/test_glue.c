#include <stdarg.h>
#include <stdio.h>
#include <sentry/ktypes.h>
#include <uapi/handle.h>

/*
 * overloading printk() with standard printf
 */
kstatus_t printk(const char *fmt __attribute__((unused)), ...) {
#if 1
    va_list args;
    va_start(args, fmt);
    vprintf(fmt, args);
    va_end(args);
#endif
    return K_STATUS_OKAY;
}
