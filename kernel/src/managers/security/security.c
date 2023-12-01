// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <sentry/ktypes.h>
#include <sentry/managers/security.h>
#include <sentry/managers/debug.h>
#include "entropy.h"

kstatus_t mgr_security_init(void)
{
    kstatus_t status;
    pr_info("initialize security manager...");
    status = mgr_security_entropy_init();
    return status;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_security_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif
