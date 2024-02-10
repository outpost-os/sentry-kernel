#ifndef LIBTEST_LOG_H
#define LIBTEST_LOG_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdarg.h>
#include <stddef.h>

#define pr_autotest_fmt(fmt) "%s: " fmt "\n", __func__

/**
 * @def autotest messages
 */
#define pr_autotest(fmt, ...) \
	printf("[AT] " pr_autotest_fmt(fmt), ##__VA_ARGS__)

#ifdef __cplusplus
}
#endif

#endif
