// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/managers/clock.h>
#include <sentry/ktypes.h>

#include <bsp/drivers/clk/rcc.h>
#include <bsp/drivers/clk/pwr.h>
#include <bsp/drivers/flash/flash.h>
#include "perfo.h"

kstatus_t mgr_clock_init(void)
{
    kstatus_t status;
    status = pwr_probe();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }
    status = flash_probe();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }
    status = rcc_probe();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }
    status = perfo_init();
end:
    return status;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_clock_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif
