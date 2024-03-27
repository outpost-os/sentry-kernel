// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef TIME_MANAGER_H
#define TIME_MANAGER_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <sentry/arch/asm-generic/tick.h>
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

kstatus_t mgr_time_delay_del_job(taskh_t job);

/**
 * @brief add a new delayed signal to the delay queue, with a delay of delay_ms
 * the kernel will emit the signal toward the target job at end time
 */
kstatus_t mgr_time_delay_add_signal(taskh_t job, uint32_t delay_ms, uint32_t sig, bool periodic);

kstatus_t mgr_time_delay_del_signal(taskh_t job, uint32_t delay_ms);

/**
 * @brief retrieve current number of cycles since boot
 */
uint64_t mgr_time_get_cycle(void);

/**
 * @brief retrieve nanoseconds elapsed since boot
 */
uint64_t mgr_time_get_nanoseconds(void);

/**
 * @brief retrieve microseconds elapsed since boot
 */
uint64_t mgr_time_get_microseconds(void);

/**
 * @brief retrieve milliseconds elapsed since boot
 */
uint64_t mgr_time_get_milliseconds(void);

static inline uint64_t __mgr_time_get_cycle(void) {
    return systime_get_cycle();
}

static inline uint64_t __mgr_time_get_microseconds(void) {
    return systime_get_microseconds();
}

static inline uint64_t __mgr_time_get_milliseconds(void) {
    return systime_get_milliseconds();
}

static inline uint64_t __mgr_time_get_nanoseconds(void) {
    return systime_get_nanoseconds();
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
