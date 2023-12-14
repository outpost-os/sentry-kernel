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
#if CONFIG_BUILD_TARGET_AUTOTEST
#include <sentry/arch/asm-generic/tick.h>
#endif

/**
 * Linux-like log levels, so that it is possible to filter-out logs
 * on serial capture, and to filter-out activated logging through Kconfig
 * LOG_LEVEL value
 */

#ifdef CONFIG_DEBUG_COLORS
#define BG_COLOR_BLACK  "\x1b[37;40m"
#define BG_COLOR_RED    "\x1b[37;41m"
#define BG_COLOR_GREEN  "\x1b[37;42m"
#define BG_COLOR_YELLOW "\x1b[37;43m"
#define BG_COLOR_BLUE   "\x1b[37;44m"
#define BG_COLOR_PURPLE "\x1b[37;45m"
#define BG_COLOR_CYAN   "\x1b[37;46m"
#define BG_COLOR_WHITE  "\x1b[37;47m"
#else
#define BG_COLOR_BLACK
#define BG_COLOR_RED
#define BG_COLOR_GREEN
#define BG_COLOR_YELLOW
#define BG_COLOR_BLUE
#define BG_COLOR_PURPLE
#define BG_COLOR_CYAN
#define BG_COLOR_WHITE
#endif

#define KERN_EMERG      "[0]"
#define KERN_ALERT      "[1]"
#define KERN_CRIT       "[2]"
#define KERN_ERR        "[3]"
#define KERN_WARNING    "[4]"
#define KERN_NOTICE     "[5]"
#define KERN_INFO       "[6]"
#define KERN_DEBUG      "[7]"

#ifdef CONFIG_BUILD_TARGET_RELEASE
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
#define pr_fmt(fmt) "%s: " fmt BG_COLOR_BLACK "\n", __func__

#if CONFIG_DEBUG_LEVEL > 0
/**
 * @def emergency messages, the system do not work correctly anymore
 */
#define pr_emerg(fmt, ...) \
	printk(BG_COLOR_RED KERN_EMERG " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_emerg(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 1
/**
 * @def alert message, the system is in alert mode, even if it may no be unstable
 */
#define pr_alert(fmt, ...) \
	printk(BG_COLOR_RED KERN_ALERT " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_alert(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 2
/**
 * @def critical error of any module
 */
#define pr_crit(fmt, ...) \
	printk(BG_COLOR_RED KERN_CRIT " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_crit(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 3
/**
 * @def something went wrong somewhere
 */
#define pr_err(fmt, ...) \
	printk(BG_COLOR_RED KERN_ERR " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_err(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 4
/**
 * @def warning information about anything (fallbacking, etc...)
 */
#define pr_warn(fmt, ...) \
	printk(BG_COLOR_PURPLE KERN_WARNING " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_warn(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 5
/**
 * @def notice on something that is a little tricky, but not a warning though
 */
#define pr_notice(fmt, ...) \
	printk(BG_COLOR_PURPLE KERN_NOTICE " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_notice(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 6
/**
 * @def usual informational messages
 */
#define pr_info(fmt, ...) \
	printk(BG_COLOR_BLUE KERN_INFO " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_info(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 7
/**
 * @def debugging messages, may generates a lot of output or performances impacts
 */
#define pr_debug(fmt, ...) \
	printk(BG_COLOR_GREEN KERN_DEBUG " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_debug(fmt, ...)
#endif

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
/** @def autotest log prefix */
#define KERN_AUTOTEST   "[T]"

/**
 * @def pr_ auto format string for pr_autotest only, adding TEST and current timestamping in u64
 * format
 */
#define pr_autotest_fmt(fmt) "%lu%lu: %s: " fmt BG_COLOR_BLACK "\n", systime_get_cycleh(),systime_get_cyclel(), __func__

/**
 * @def autotest messages, for autotest functions only
 */
#define pr_autotest(fmt, ...) \
	printk(BG_COLOR_CYAN KERN_AUTOTEST " " pr_autotest_fmt(fmt), ##__VA_ARGS__)
#endif

kstatus_t mgr_debug_autotest(void);
#endif

kstatus_t mgr_debug_init(void);

#ifdef __cplusplus
}
#endif

#endif/*!DEBUG_MANAGER_H*/
