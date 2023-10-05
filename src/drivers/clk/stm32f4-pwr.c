// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file STM32F3xx and F4xx PLL & clock driver (see ST RM0090 datasheet)
 */
#include <assert.h>

#include <sentry/arch/asm-cortex-m/soc.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/arch/asm-cortex-m/buses.h>
#include <sentry/arch/asm-generic/membarriers.h>
#include <sentry/io.h>
#include <sentry/bits.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/clk/pwr.h>
#include "pwr_defs.h"

kstatus_t pwr_probe(void)
{
    /*
     * This bit controls the main internal voltage regulator output
     * voltage to achieve a trade-off between performance and power
     * consumption when the device does not operate at the maximum
     * frequency. (DocID018909 Rev 15 - page 141)
     * PWR_CR_VOS = 1 => Scale 1 mode (default value at reset)
     */
    return pwr_set_voltage_regulator_scaling(POWER_VOS_SCALE_1);
}

/*@
  @ requires scale_is_valid(scale);
  */
kstatus_t pwr_set_voltage_regulator_scaling(uint8_t scale)
{
    kstatus_t status;
    size_t reg;
    reg = ioread32(PWR_BASE_ADDR + PWR_CR_REG);
    reg &= ~PWR_CR_VOS_MASK;
    reg |= ((scale << PWR_CR_VOS_SHIFT) & PWR_CR_VOS_MASK);
    iowrite32(PWR_BASE_ADDR + PWR_CR_REG, reg);
    status = K_STATUS_OKAY;
    return status;
}
