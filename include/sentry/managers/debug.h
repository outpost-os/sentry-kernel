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
#include <sentry/ktypes.h>


#ifndef CONFIG_BUILD_TARGET_DEBUG
/* in non-debug mode, no debug */
static inline kstatus_t printk(const char* fmt __attribute__((unused)), ...) {
    return K_STATUS_OKAY;
}
#else
kstatus_t printk(const char* fmt, ...);
#endif

kstatus_t mgr_debug_init(void);

#ifdef __cplusplus
}
#endif

#endif/*!DEBUG_MANAGER_H*/
