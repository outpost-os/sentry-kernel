// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <sentry/arch/asm-generic/tick.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/ktypes.h>
#include <sentry/managers/time.h>
#include <sentry/managers/debug.h>
#include <sentry/sched.h>
#include "delay.h"

/**
  * @brief initialize the time manager
  *
  * @return K_STATUS_OKAY on success, or various error types
  */
kstatus_t mgr_time_init(void)
{
    kstatus_t status;
    mgr_time_delay_flush();
    /* initialize platform ticker */
    systick_init();
    /* initialize scheduler */
    if (unlikely((status = sched_init()) != K_STATUS_OKAY)) {
        pr_emerg("failed to init scheduler!");
        panic(PANIC_KERNEL_INVALID_MANAGER_STATE);
        goto err;
    }
err:
    return status;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
/**
  * @brief autotesting time manager
  */
kstatus_t mgr_time_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif
