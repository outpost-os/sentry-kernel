// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef UAPI_AUTOTEST_H
#define UAPI_AUTOTEST_H

#include <stdint.h>

/** FIXME: this header is to be replaced by the rust equivalent in the UAPI
 * implementation. The C header (uapi.h) will be generated.
 */

/**
 * @file Sentry autotest-specific flags for autotest syscall
 *
 * This syscall is a special case: it is only added in AUTOTEST mode, and
 * allow a control plane support for the autotest application.
 * In autotest mode, the Sentry kernel is built with a forced application layout
 * in which only autotest and idle applications exist. It can be done with Sentry
 * alone without any project repository.
 * This syscall is used in association wih the sys_wait_for_event() syscall, through
 * which the kernel returns the result of each autotest to the autotest task.
 *
 * In autotest mode, the kernel is configured harden so that it mimic as short as
 * possible the production mode, but the panic handle emit signals to the autotest
 * app instead of resetting the board.
 *
 * The autotest app can:
 *  * use the sys_autotest() syscall to ask the kernel for kernel-side checks
 *  * use other syscalls in various manners, even fuzzing, as the kernel will always
 *    respond in a panic() to signal manner toward the autotest application.
 *
 * The autotest app can prepare the test-bed at first, typically to map an external
 * console or serial link for tests transmission, deported control plane, or logging.
 */
typedef enum autotest_request {
    /**< entering autotest mode. Allows nominal test-bed config before autotests
       for e.g. test fixtures that need standard syscall usage. From now on, panic
       is redirect to signal-to-autotest */
    SENTRY_AUTOTEST_ENTER  = 1,
    /**< leaving test mode. panic behave normally */
    SENTRY_AUTOTEST_LEAVE,
    SENTRY_AUTOTEST_MGR_CLOCK,     /**< ask for clock mgr autotest */
    SENTRY_AUTOTEST_MGR_DEBUG,     /**< ask for debug mgr autotest */
    SENTRY_AUTOTEST_MGR_DEVICE,    /**< ask for device mgr autotest */
    SENTRY_AUTOTEST_MGR_INTERRUPT, /**< ask for interrupt mgr autotest */
    SENTRY_AUTOTEST_MGR_IO,        /**< ask for IO manager autotest */
    SENTRY_AUTOTEST_MGR_MEMORY,    /**< ask for IO memory autotest */
    SENTRY_AUTOTEST_MGR_SECURITY,  /**< ask for security manager autotest */
    SENTRY_AUTOTEST_MGR_TASK,      /**< ask for task manager autotest */
    SENTRY_AUTOTEST_SCHED,         /**< ask for scheduler autotest */
} autotest_request_t;

#endif /*!UAPI_AUTOTEST_H*/
