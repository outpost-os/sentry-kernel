// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/usart/usart.h>
#include <bsp/drivers/clk/rcc.h>

/**
 * @brief probe the debug backend
 *
 * by now, only kernel serial output is probbed. Other debug I/O can be
 * imagined/configured, such as leds, etc...
 */
kstatus_t mgr_debug_init(void)
{
    kstatus_t status;
    status = usart_probe();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }
#if CONFIG_BUILD_TARGET_DEBUG
    rcc_enable_debug_clockout();
#endif
end:
    return status;
}
