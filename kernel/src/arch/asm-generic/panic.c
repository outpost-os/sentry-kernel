// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/arch/asm-generic/panic.h>
#include <sentry/managers/debug.h>
#include <sentry/managers/task.h>
#include <uapi/uapi.h>
#include <uapi/handle.h>

#ifndef CONFIG_BUILD_TARGET_RELEASE
/* pretty printing rodata content, not in release mode */
static const char* panic_events_name[] = {
    "USER_HARDFAULT",
    "KERNEL_HARDFAULT",
    "USER_BUSFAULT",
    "KERNEL_BUSFAULT",
    "USER_USAGEFAULT",
    "KERNEL_USAGEFAULT",
    "USER_MEMACCESS",
    "KERNEL_MEMACCESS",
    "KERNEL_INVALID_USERSPACE_INPUT",
    "KERNEL_SHORTER_KBUFFERS_CONFIG",
    "KERNEL_INVALID_MANAGER_STATE",
    "KERNEL_INVALID_MANAGER_RESPONSE",
    "KERNEL_TIMEOUT",
    "KERNEL_BAD_CFI_CALCULATION",
    "HARDWARE_INVALID_STATE",
    "HARDWARE_UNEXPECTED_MODIFICATION",
    "PANIC_CONFIGURATION_MISMATCH",
};
#endif

/**
 * @brief pretty printing of panic event, only in non-release mode
 */
void panic_print_event(panic_event_t ev) {
#ifndef CONFIG_BUILD_TARGET_RELEASE
    if (unlikely(ev >= PANIC_EVENT_MAX)) {
        return;
    }
    pr_debug("panic event: PANIC_%s", panic_events_name[ev]);
#endif
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
/**
 * @brief emitting signal to autotest task corresponding to current panic event
 */
kstatus_t panic_emit_signal(panic_event_t ev)
{
    taskh_t autotest = mgr_task_get_autotest();
    return mgr_task_push_sig_event((uint32_t)(ev + SIGNAL_USR2 + 1), 0UL, autotest);
}
#endif
