// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/security.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/sched.h>

stack_frame_t *gate_start(stack_frame_t *frame, uint32_t target_label)
{
    taskh_t current = sched_get_current();
    stack_frame_t *next_frame = frame;
    taskh_t target_handle;
    const task_meta_t *meta;

    if (unlikely(mgr_security_has_capa(current,  CAP_SYS_PROCSTART) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(mgr_task_get_handle(target_label, &target_handle) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(sched_schedule(target_handle) != K_STATUS_OKAY)) {
        /* scheduler list must always be able to schedule tasks */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
}
