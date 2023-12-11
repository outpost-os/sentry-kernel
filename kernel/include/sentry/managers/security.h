#ifndef SECURITY_MANAGER_H
#define SECURITY_MANAGER_H

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @file Sentry I/O manager API
 */

#include <sentry/ktypes.h>

kstatus_t mgr_security_init(void);

kstatus_t mgr_security_entropy_generate(uint32_t *seed);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_security_autotest(void);
#endif

#ifdef __cplusplus
}
#endif

#endif/*!SECURITY_MANAGER_H*/
