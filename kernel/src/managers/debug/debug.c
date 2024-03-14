// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/usart/usart.h>
#include <bsp/drivers/clk/rcc.h>
#include "log.h"

/**
 * @brief probe the debug backend
 *
 * by now, only kernel serial output is probbed. Other debug I/O can be
 * imagined/configured, such as leds, etc...
 */
kstatus_t mgr_debug_init(void)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_DEBUG_OUTPUT_USART
    status = usart_probe();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }
#endif
#ifdef CONFIG_BUILD_TARGET_DEBUG
    status = rcc_enable_debug_clockout();
#endif
    dbgbuffer_flush();
#if CONFIG_DEBUG_OUTPUT_USART
end:
#endif
    return status;
}

/**
 * @brief raw log export, abstracting the selected output log device
 *
 * typically used for sys_log() syscall as no parsing is made in kernelspace
 *
 * @param[in] logbuf: input log buffer
 * @param[in] len: log buffer len
 */
kstatus_t debug_rawlog(const uint8_t *logbuf, size_t len)
{
	return usart_tx(logbuf, len);
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_debug_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif
