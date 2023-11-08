// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef DEBUG_MANAGER_H
#define DEBUG_MANAGER_H

#ifdef __cplusplus
extern "C" {
#endif
/**
 * @file Sentry Debug manager
 */
#include <stdarg.h>
#include <stddef.h>
#include <sentry/ktypes.h>

/**
 * Linux-like log levels, so that it is possible to filter-out logs
 * on serial capture, and to filter-out activated logging through Kconfig
 * LOG_LEVEL value
 */

#define KERN_EMERG      "[0]"
#define KERN_ALERT      "[1]"
#define KERN_CRIT       "[2]"
#define KERN_ERR        "[3]"
#define KERN_WARNING    "[4]"
#define KERN_NOTICE     "[5]"
#define KERN_INFO       "[6]"
#define KERN_DEBUG      "[7]"

#ifndef CONFIG_BUILD_TARGET_DEBUG
/* in non-debug mode, no debug */

static inline kstatus_t debug_rawlog(const uint8_t *logbuf __attribute__((unused)), size_t len __attribute__((unused))) {
	return K_STATUS_OKAY;
}

static inline kstatus_t printk(const char* fmt __attribute__((unused)), ...) {
    return K_STATUS_OKAY;
}
#define pr_emerg(fmt, ...)
#define pr_alert(fmt, ...)
#define pr_crit(fmt, ...)
#define pr_err(fmt, ...)
#define pr_warn(fmt, ...)
#define pr_notice(fmt, ...)
#define pr_info(fmt, ...)
#define pr_debug(fmt, ...)

#else
/*
 * user log output, no parsing, direct debug output transission
 */
kstatus_t debug_rawlog(const uint8_t *logbuf, size_t len);

/* kernel printk() behave like printf() and thus do not add carriage return
 * at end of lines by itself. Although, it is highly recommanded not to
 * directly use printk() but instead use brelow pr_xxx upper layer API,
 * that forge log format, add carriage return, and allows auto-filter out
 * based on current log level
*/
kstatus_t printk(const char* fmt, ...);

/**
 * @def pr_ auto format string for all pr_xxx API. Not to be used directly
 */
#define pr_fmt(fmt) "%s: " fmt "\n", __func__

/**
 * @def emergency messages, the system do not work correctly anymore
 */
#define pr_emerg(fmt, ...) \
	printk(KERN_EMERG " " pr_fmt(fmt), ##__VA_ARGS__)

/**
 * @def alert message, the system is in alert mode, even if it may no be unstable
 */
#define pr_alert(fmt, ...) \
	printk(KERN_ALERT " " pr_fmt(fmt), ##__VA_ARGS__)

/**
 * @def critical error of any module
 */
#define pr_crit(fmt, ...) \
	printk(KERN_CRIT " " pr_fmt(fmt), ##__VA_ARGS__)

/**
 * @def something went wrong somewhere
 */
#define pr_err(fmt, ...) \
	printk(KERN_ERR " " pr_fmt(fmt), ##__VA_ARGS__)

/**
 * @def warning information about anything (fallbacking, etc...)
 */
#define pr_warn(fmt, ...) \
	printk(KERN_WARNING " " pr_fmt(fmt), ##__VA_ARGS__)

/**
 * @def notice on something that is a little tricky, but not a warning though
 */
#define pr_notice(fmt, ...) \
	printk(KERN_NOTICE " " pr_fmt(fmt), ##__VA_ARGS__)

/**
 * @def usual informational messages
 */
#define pr_info(fmt, ...) \
	printk(KERN_INFO " " pr_fmt(fmt), ##__VA_ARGS__)

/**
 * @def debugging messages, may generates a lot of output or performances impacts
 */
#define pr_debug(fmt, ...) \
	printk(KERN_DEBUG " " pr_fmt(fmt), ##__VA_ARGS__)

#endif

kstatus_t mgr_debug_init(void);

#ifdef __cplusplus
}
#endif

#endif/*!DEBUG_MANAGER_H*/
