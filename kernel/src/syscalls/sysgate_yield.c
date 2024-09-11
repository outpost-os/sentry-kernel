// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/sched.h>

stack_frame_t *gate_yield(stack_frame_t *frame)
{
    taskh_t current = sched_get_current();
    taskh_t next;
    stack_frame_t *next_frame = frame;

    next = sched_elect();
    if (unlikely(mgr_task_get_sp(next, &next_frame) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
    return next_frame;
}
