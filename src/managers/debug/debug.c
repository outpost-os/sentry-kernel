// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/usart/usart.h>

/**
 * @brief probe the debug backend
 *
 * by now, only kernel serial output is probbed. Other debug I/O can be
 * imagined/configured, such as leds, etc...
 */
kstatus_t mgr_debug_probe(void)
{
    return usart_probe();
}
