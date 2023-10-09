// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef DRV_RCC_H
#define DRV_RCC_H

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
 * @brief Probe and reset the RCC clock configuration
 */
kstatus_t rcc_probe(void);

/**
 * @brief get current core frequency in Hertz
 */
uint64_t rcc_get_core_frequency(void);

kstatus_t rcc_enable_apbx(void);

kstatus_t rcc_disable_apbx(void);

kstatus_t rcc_enable(bus_id_t busid, uint32_t clk_msk, rcc_opts_t flags);

kstatus_t rcc_disable(bus_id_t busid, uint32_t clk_msk, rcc_opts_t flags);

kstatus_t rcc_get_bus_clock(bus_id_t busid, uint32_t *busclk);



#endif/*DRV_RCC_H*/