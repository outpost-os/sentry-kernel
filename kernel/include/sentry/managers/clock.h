// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef CLOCK_MANAGER_H
#define CLOCK_MANAGER_H

/**
 * @file Sentry Clock manager
 */
#include <uapi/handle.h>
#include <sentry/ktypes.h>

#ifdef __cplusplus
extern "C" {
#endif

kstatus_t mgr_clock_init(void);

uint32_t mgr_clock_get_cycle_per_usec(void);

uint64_t mgr_clock_get_cycle(void);

kstatus_t mgr_clock_enable_device(devh_t dev);

kstatus_t mgr_clock_disable_device(devh_t dev);

kstatus_t mgr_clock_configure_clockline(uint32_t clk_reg, uint32_t clkmsk, uint32_t val);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_clock_autotest(void);
#endif

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif/*!CLOCK_MANAGER_H*/
