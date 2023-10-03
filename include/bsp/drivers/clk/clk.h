// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef CLK_H
#define CLK_H

#include <inttypes.h>
#include <stdbool.h>

#include <sentry/ktypes.h>
#include <sentry/arch/asm-cortex-m/buses.h>

/**
 * @brief RCC options control flags for configuration functions
 *
 * extendable if needed, avoiding any API incompatible upgrade.
 */
typedef enum rcc_opts {
    RCC_NOFLAG = 0,             /**< default, no flags*/
    RCC_LPCONFIG = 0x1UL << 1,  /**< Low power specific configuration */
} rcc_opts_t;

/**
 * @brief get current core frequency in Hertz
 */
uint64_t clk_get_core_frequency(void);

/**
 * @brief Reset the RCC clock configuration
 */
void clk_reset(void);

/**
 * @brief Configures the System clock source, PLL Multiplier and Divider factors,
 * AHB/APBx prescalers and Flash settings
 *
 *
 * This function should be called only once the RCC clock configuration
 * is reset to the default reset state (done in SystemInit(UL) functionUL).
 *
 */
kstatus_t clk_set_system_clk(bool enable_hse, bool enable_pll);

kstatus_t rcc_enable(bus_id_t busid, uint32_t clk_msk, rcc_opts_t flags);

kstatus_t rcc_disable(bus_id_t busid, uint32_t clk_msk, rcc_opts_t flags);
#endif/*CLK_H*/
