// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/time.h>
#include <sentry/arch/asm-generic/panic.h>
#include <uapi/types.h>
#include <sentry/sched.h>

stack_frame_t *gate_alarm(stack_frame_t *frame, uint32_t delay_ms, uint32_t flag)
{
    taskh_t current = sched_get_current();
    taskh_t next;
    stack_frame_t *next_frame = frame;

    switch (flag) {
        case O_ALRM_START:
            if (unlikely(mgr_time_delay_add_signal(current, delay_ms, SIGNAL_ALARM, false) != K_STATUS_OKAY)) {
                mgr_task_set_sysreturn(current, STATUS_BUSY);
                goto end;
            }
            mgr_task_set_sysreturn(current, STATUS_OK);
            break;
        case O_ALRM_START_PERIODIC:
            if (unlikely(mgr_time_delay_add_signal(current, delay_ms, SIGNAL_ALARM, true) != K_STATUS_OKAY)) {
                mgr_task_set_sysreturn(current, STATUS_BUSY);
                goto end;
            }
            mgr_task_set_sysreturn(current, STATUS_OK);
            break;
        case O_ALRM_STOP:
            if (unlikely(mgr_time_delay_del_signal(current, delay_ms) != K_STATUS_OKAY)) {
                mgr_task_set_sysreturn(current, STATUS_NO_ENTITY);
                goto end;
            }
            mgr_task_set_sysreturn(current, STATUS_OK);
            break;
        default:
            mgr_task_set_sysreturn(current, STATUS_INVALID);
            break;
    }
end:
    return next_frame;
}
