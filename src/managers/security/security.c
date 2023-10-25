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
    printk("initialize security manager...\n");
    status = mgr_security_entropy_init();
    return status;
}
