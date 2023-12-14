// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef TIME_MANAGER_H
#define TIME_MANAGER_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <sentry/arch/asm-generic/tick.h>
#include <bsp/drivers/clk/rcc.h>
#include <sentry/managers/task.h>
#include <uapi/handle.h>

kstatus_t mgr_time_init(void);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_time_autotest(void);
#endif

/**
 * @brief add a new delayed job to the delay queue, with a delay of delay_ms
 */
kstatus_t mgr_time_delay_add_job(taskh_t job, uint32_t delay_ms);

/**
 * @brief add a new delayed signal to the delay queue, with a delay of delay_ms
 * the kernel will emit the signal toward the target job at end time
 */
kstatus_t mgr_time_delay_add_signal(taskh_t job, uint32_t delay_ms, sigh_t sig);


static inline uint64_t mgr_time_get_cycle(void) {
    uint64_t ts = systime_get_cycleh();
    ts <<= 32;
    ts |= systime_get_cyclel();
    return ts;
}

static inline uint64_t mgr_time_get_micro(void) {
    uint64_t ts = systime_get_cycleh();
    uint32_t freq = rcc_get_core_frequency();
    /* divide freq by number of micros in 1 sec */
    freq /= 1000000UL;
    ts <<= 32;
    ts |= systime_get_cyclel();
    ts /= freq;
    return ts;
}

static inline uint64_t mgr_time_get_milli(void) {
    uint64_t ts = systime_get_cycleh();
    uint32_t freq = rcc_get_core_frequency();
    /* divide freq by number of millis in 1 sec */
    freq /= 1000UL;
    ts <<= 32;
    ts |= systime_get_cyclel();
    ts /= freq;
    return ts;
}
/**
 * delay ticker, to be called by the systick using JIFFIES_TO_MSEC(1)
 * to calculate back the ticker period
 */
void mgr_time_delay_tick(void);

#if defined(__cplusplus)
}
#endif

#endif/*!TIME_MANAGER_H*/
