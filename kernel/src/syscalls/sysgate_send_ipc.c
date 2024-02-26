#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/sched.h>


stack_frame_t *gate_send_ipc(stack_frame_t *frame, taskh_t target, uint32_t len)
{
    stack_frame_t *next_frame = frame;
    taskh_t current = sched_get_current();
    job_state_t dest_state;
    if (unlikely(len > CONFIG_SVC_EXCHANGE_AREA_LEN)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(mgr_task_handle_exists(target) == SECURE_FALSE)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* TODO: deadlock detecion */

    if (unlikely(mgr_task_push_ipc_event(len, current, target) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_BUSY);
        goto end;
    }
    mgr_task_get_state(target, &dest_state);
    if (dest_state != JOB_STATE_IPC_SEND_BLOCKED) {
        /* awake target job only if not already blocked by another sending event */
        mgr_task_set_state(target, JOB_STATE_READY);
        sched_schedule(target);
    }
    /* as IPC return call is asynchronously set, set NON_SENSE as default */
    mgr_task_set_sysreturn(current, STATUS_NON_SENSE);
end:
    return next_frame;
}
