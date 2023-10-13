#ifndef DEBUG_MANAGER_H
#define DEBUG_MANAGER_H

/**
 * @file Sentry Debug manager
 */
#include <stdarg.h>
#include <sentry/ktypes.h>


#ifndef CONFIG_BUILD_TARGET_DEBUG
/* in non-debug mode, no debug */
static inline kstatus_t printk(const char* fmt, ...) {
    return K_STATUS_OKAY;
}
#else
kstatus_t printk(const char* fmt, ...);
#endif

#include <sentry/ktypes.h>
