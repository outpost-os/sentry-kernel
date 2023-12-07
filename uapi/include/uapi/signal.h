// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef UAPI_SIGNAL_H
#define UAPI_SIGNAL_H

#include <stdint.h>

typedef enum signal {
    SIGNAL_ABORT = 0,   /**< Abort signal */
    SIGNAL_ALARM,       /**< timer (from alarm) */
    SIGNAL_BUS,         /**< bus error (bad memory access, memory required)*/
    SIGNAL_CONT,        /**< continue if previously stopped */
    SIGNAL_ILL,         /**< illegal instruction. Can be also used for upper protocols */
    SIGNAL_IO,          /**< I/O now ready */
    SIGNAL_PIPE,        /**< broken pipe */
    SIGNAL_POLL,        /**< event pollable */
    SIGNAL_TERM,        /**< termination signal. Can be used to stop an IPC stream for e.g. (remote process termination is not possible) */
    SIGNAL_TRAP,        /**< trace/bp signal (debug usage )*/
    SIGNAL_USR1,        /**< 1st user-defined signal */
    SIGNAL_USR2,        /**< 2nd user-defined signal */
#ifdef CONFIG_BUILD_TARGET_AUTOTEST
    /* in autotest mode, panic event is pushed as a signal value to autotest app */
    SIGNAL_PANIC_USER_HARDFAULT,
    SIGNAL_PANIC_KERNEL_HARDFAULT,
    SIGNAL_PANIC_USER_BUSFAULT,
    SIGNAL_PANIC_KERNEL_BUSFAULT,
    SIGNAL_PANIC_USER_USAGEFAULT,
    SIGNAL_PANIC_KERNEL_USAGEFAULT,
    SIGNAL_PANIC_USER_MEMACCESS,
    SIGNAL_PANIC_KERNEL_MEMACCESS,
    SIGNAL_PANIC_KERNEL_INVALID_USERSPACE_INPUT,
    SIGNAL_PANIC_KERNEL_SHORTER_KBUFFERS_CONFIG,
    SIGNAL_PANIC_KERNEL_INVALID_MANAGER_STATE,
    SIGNAL_PANIC_KERNEL_INVALID_MANAGER_RESPONSE,
    SIGNAL_PANIC_KERNEL_TIMEOUT,
    SIGNAL_PANIC_KERNEL_BAD_CFI_CALCULATION,
    SIGNAL_PANIC_HARDWARE_INVALID_STATE,
    SIGNAL_PANIC_HARDWARE_UNEXPECTED_MODIFICATION,
    SIGNAL_AUTOTEST_DONE,
    SIGNAL_AUTOTEST_FAILED,
    SIGNAL_AUTOTEST_TIMEOUTED,
#endif
} signal_t;

#endif/*!UAPI_SIGNAL_H*/
