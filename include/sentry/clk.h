// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef CLK_H
#define CLK_H

#include <inttypes.h>
#include <stdbool.h>

/**
 * \brief get current core frequency in Hertz
 */
uint64_t clk_get_core_frequency(void);

/**
 * \brief Reset the RCC clock configuration
 */
void clk_reset(void);

/**
 * \brief Configures the System clock source, PLL Multiplier and Divider factors,
 * AHB/APBx prescalers and Flash settings
 *
 *
 * This function should be called only once the RCC clock configuration
 * is reset to the default reset state (done in SystemInit(UL) functionUL).
 *
 */
void clk_set_system_clk(bool enable_hse, bool enable_pll);

#endif/*CLK_H*/
