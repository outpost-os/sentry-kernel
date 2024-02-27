#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/sched.h>
#include <uapi/types.h>


stack_frame_t *gate_waitforevent(stack_frame_t *frame,
                               uint8_t       mask,
                               uint32_t      timeout)

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
        goto end;
    }
    /* and then irq... */
    if (mask & EVENT_TYPE_IRQ) {
        if (mgr_task_load_int_event(current) == K_STATUS_OKAY) {
            mgr_task_set_sysreturn(current, STATUS_OK);
            goto end;
        }
    }
    /* and then ipc... */
    if (mask & EVENT_TYPE_IPC) {
        if (mgr_task_load_ipc_event(current) == K_STATUS_OKAY) {
            mgr_task_set_sysreturn(current, STATUS_OK);
            goto end;
        }
        goto end;
    }
    /* no event at all... schedule */
    mgr_task_set_state(current, JOB_STATE_WAITFOREVENT);
    next = sched_elect();
    mgr_task_get_sp(next, &next_frame);
end:
    return next_frame;
}
