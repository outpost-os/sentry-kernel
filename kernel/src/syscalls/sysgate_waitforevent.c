// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/time.h>
#include <sentry/sched.h>
#include <uapi/types.h>


stack_frame_t *gate_waitforevent(stack_frame_t *frame,
                               uint8_t          mask,
                               int32_t          timeout)

{
    taskh_t current = sched_get_current();
    taskh_t next;
    stack_frame_t *next_frame = frame;
    /* ordered check of events, starting with signal... */
    if (mask & EVENT_TYPE_SIGNAL) {
        if (mgr_task_load_sig_event(current) == K_STATUS_OKAY) {
            mgr_task_set_sysreturn(current, STATUS_OK);
            goto end;
        }
    }
    /* and then irq... */
    if (mask & EVENT_TYPE_IRQ) {
        uint32_t irqn;
        if (mgr_task_load_int_event(current, &irqn) == K_STATUS_OKAY) {
            /* TODO: copy IRQn to user */
            mgr_task_set_sysreturn(current, STATUS_OK);
            goto end;
        }
    }
#if CONFIG_HAS_GPDMA
    if (mask & EVENT_TYPE_DMA) {
        dmah_t dmah;
        dma_chan_state_t event;
        if (mgr_task_load_dma_event(current, &dmah, &event) == K_STATUS_OKAY) {
            /* TODO: copy handle  to user */
            mgr_task_set_sysreturn(current, STATUS_OK);
            goto end;
        }
    }
#endif
    /* and then ipc... */
    if (mask & EVENT_TYPE_IPC) {
        if (mgr_task_load_ipc_event(current) == K_STATUS_OKAY) {
            mgr_task_set_sysreturn(current, STATUS_OK);
            goto end;
        }
    }
    if (timeout == -1) {
        /* do not deschedule the job */
        mgr_task_set_sysreturn(current, STATUS_AGAIN);
        goto end;
    }
    if (timeout > 0) {
        mgr_time_delay_add_job(current, timeout);
    }
    /* no event at all... delaying if timeout, and schedule */
    mgr_task_set_state(current, JOB_STATE_WAITFOREVENT);
    mgr_task_set_sysreturn(current, STATUS_NON_SENSE);
    next = sched_elect();
    mgr_task_get_sp(next, &next_frame);
end:
    return next_frame;
}
