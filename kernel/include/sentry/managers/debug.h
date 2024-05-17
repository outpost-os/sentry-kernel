// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef DEBUG_MANAGER_H
#define DEBUG_MANAGER_H

/**
 * @file Sentry Debug manager
 */
#include <stdarg.h>
#include <stddef.h>
#include <sentry/ktypes.h>
#if CONFIG_BUILD_TARGET_AUTOTEST
#include <sentry/arch/asm-generic/tick.h>
#endif

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Linux-like log levels, so that it is possible to filter-out logs
 * on serial capture, and to filter-out activated logging through Kconfig
 * LOG_LEVEL value
 */

#if defined(CONFIG_DEBUG_COLORS_BACKGROUND)
/* colored BG, FG is adapted */
#define COLOR_BLACK  "\x1b[37;40m"
#define COLOR_RED    "\x1b[37;41m"
#define COLOR_GREEN  "\x1b[30;42m"
#define COLOR_YELLOW "\x1b[37;43m"
#define COLOR_BLUE   "\x1b[37;44m"
#define COLOR_PURPLE "\x1b[37;45m"
#define COLOR_CYAN   "\x1b[30;46m"
#define COLOR_WHITE  "\x1b[30;47m"
#elif defined(CONFIG_DEBUG_COLORS_REGULAR)
#define COLOR_BLACK  "\x1b[0;30m"
#define COLOR_RED    "\x1b[0;31m"
#define COLOR_GREEN  "\x1b[0;32m"
#define COLOR_YELLOW "\x1b[0;33m"
#define COLOR_BLUE   "\x1b[0;34m"
#define COLOR_PURPLE "\x1b[0;35m"
#define COLOR_CYAN   "\x1b[0;36m"
#define COLOR_WHITE  "\x1b[0;37m"
#elif defined(CONFIG_DEBUG_COLORS_BOLD)
#define COLOR_BLACK  "\x1b[0;30m" /* no bold for black (reset case) */
#define COLOR_RED    "\x1b[1;31m"
#define COLOR_GREEN  "\x1b[1;32m"
#define COLOR_YELLOW "\x1b[1;33m"
#define COLOR_BLUE   "\x1b[1;34m"
#define COLOR_PURPLE "\x1b[1;35m"
#define COLOR_CYAN   "\x1b[1;36m"
#define COLOR_WHITE  "\x1b[0;37m" /* no bold for white (reset case)*/
#else
#define COLOR_BLACK
#define COLOR_RED
#define COLOR_GREEN
#define COLOR_YELLOW
#define COLOR_BLUE
#define COLOR_PURPLE
#define COLOR_CYAN
#define COLOR_WHITE

#endif
#if defined(CONFIG_DEBUG_COLOR_DEFAULT_WHITE)
#define COLOR_RESET  COLOR_WHITE
#else
#define COLOR_RESET  COLOR_BLACK
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
#define pr_autotest(fmt, ...)

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
#define pr_fmt(fmt) "%s: " fmt COLOR_RESET "\n", __func__

#if CONFIG_DEBUG_LEVEL > 0
/**
 * @def emergency messages, the system do not work correctly anymore
 */
#define pr_emerg(fmt, ...) \
	printk(COLOR_RED KERN_EMERG " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_emerg(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 1
/**
 * @def alert message, the system is in alert mode, even if it may no be unstable
 */
#define pr_alert(fmt, ...) \
	printk(COLOR_RED KERN_ALERT " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_alert(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 2
/**
 * @def critical error of any module
 */
#define pr_crit(fmt, ...) \
	printk(COLOR_RED KERN_CRIT " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_crit(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 3
/**
 * @def something went wrong somewhere
 */
#define pr_err(fmt, ...) \
	printk(COLOR_RED KERN_ERR " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_err(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 4
/**
 * @def warning information about anything (fallbacking, etc...)
 */
#define pr_warn(fmt, ...) \
	printk(COLOR_PURPLE KERN_WARNING " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_warn(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 5
/**
 * @def notice on something that is a little tricky, but not a warning though
 */
#define pr_notice(fmt, ...) \
	printk(COLOR_PURPLE KERN_NOTICE " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_notice(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 6
/**
 * @def usual informational messages
 */
#define pr_info(fmt, ...) \
	printk(COLOR_BLUE KERN_INFO " " pr_fmt(fmt), ##__VA_ARGS__)
#else
#define pr_info(fmt, ...)
#endif

#if CONFIG_DEBUG_LEVEL > 7
/**
 * @def debugging messages, may generates a lot of output or performances impacts
 */
#define pr_debug(fmt, ...) \
	printk(COLOR_GREEN KERN_DEBUG " " pr_fmt(fmt), ##__VA_ARGS__)
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
#define pr_autotest_fmt(fmt) "%lu%lu: %s: " fmt COLOR_RESET "\n", systime_get_cycleh(),systime_get_cyclel(), __func__

/**
 * @def autotest messages, for autotest functions only
 */
#define pr_autotest(fmt, ...) \
	printk(COLOR_CYAN KERN_AUTOTEST " " pr_autotest_fmt(fmt), ##__VA_ARGS__)
#else
/* in debug mode, pr_autotest do nothing */
#define pr_autotest(fmt, ...)

#endif

kstatus_t mgr_debug_autotest(void);
#endif/*autotest */



kstatus_t mgr_debug_init(void);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif/*!DEBUG_MANAGER_H*/
