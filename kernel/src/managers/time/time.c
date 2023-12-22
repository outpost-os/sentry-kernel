// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <sentry/arch/asm-generic/tick.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/ktypes.h>
#include <sentry/managers/time.h>
#include <sentry/managers/debug.h>
#include <sentry/sched.h>
#include "delay.h"

/**
  * @brief initialize the time manager
  *
  * @return K_STATUS_OKAY on success, or various error types
  */
kstatus_t mgr_time_init(void)
{
    kstatus_t status;
    mgr_time_delay_flush();
    /* initialize platform ticker */
    systime_init();
    /* initialize scheduler */
    if (unlikely((status = sched_init()) != K_STATUS_OKAY)) {
        pr_emerg("failed to init scheduler!");
        panic(PANIC_KERNEL_INVALID_MANAGER_STATE);
        goto err;
    }
err:
    return status;
}

/**
  * This function is an export of its static inline version
  * because `bindgen` would not be able to see it otherwise
  *
  * @return number of cycles elapsed since boot
  */
uint64_t mgr_time_get_cycle(void) {
    return __mgr_time_get_cycle();
}

/**
  * This function is an export of its static inline version
  * because `bindgen` would not be able to see it otherwise
  *
  * @return number of nanoseconds elapsed since boot
  */
uint64_t mgr_time_get_nanoseconds(void) {
    return __mgr_time_get_nanoseconds();
}

/**
  * This function is an export of its static inline version
  * because `bindgen` would not be able to see it otherwise
  *
  * @return number of microseconds elapsed since boot
  */
uint64_t mgr_time_get_microseconds(void) {
    return __mgr_time_get_microseconds();
}

/**
  * This function is an export of its static inline version
  * because `bindgen` would not be able to see it otherwise
  *
  * @return number of milliseconds elapsed since boot
  */
uint64_t mgr_time_get_milliseconds(void) {
    return __mgr_time_get_milliseconds();
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
/**
  * @brief autotesting time manager
  */
kstatus_t mgr_time_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif
