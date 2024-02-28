#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/sched.h>


stack_frame_t *gate_send_ipc(stack_frame_t *frame, taskh_t target, uint32_t len)
{
    stack_frame_t *next_frame = frame;
    taskh_t current = sched_get_current();
    taskh_t next;
    job_state_t dest_state;
    /* sanitize first */
    if (unlikely(len > (CONFIG_SVC_EXCHANGE_AREA_LEN - sizeof(exchange_event_t)))) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto err;
    }
    if (unlikely(mgr_task_handle_exists(target) == SECURE_FALSE)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto err;
    }
    /* TODO: deadlock detecion */

    /* push IPC event to target */
    if (unlikely(mgr_task_push_ipc_event(len, current, target) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_BUSY);
        goto err;
    }
    /* except in autotest mode, a job can't send a message to itself */
    if (unlikely(current == target)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto err_autotest;
    }
    /* lock current job */
    mgr_task_set_state(current, JOB_STATE_IPC_SEND_BLOCKED);
    /* as IPC return call is asynchronously set, set NON_SENSE as default */
    mgr_task_set_sysreturn(current, STATUS_NON_SENSE);
    /* check if target can be sheduled again */
    mgr_task_get_state(target, &dest_state);
    if ((dest_state != JOB_STATE_IPC_SEND_BLOCKED) &&
        (dest_state != JOB_STATE_SLEEPING_DEEP)) {
        /* awake target job only if not already waiting for another IPC and if
         * not in deep sleep
         */
        if (dest_state == JOB_STATE_SLEEPING) {
            /* if target job was sleeping, set return to ok */
            /* FIXME: define a dedicated return code */
            mgr_task_set_sysreturn(target, STATUS_OK);
            mgr_task_set_state(target, JOB_STATE_READY);
            sched_schedule(target);
        }
    }
    next = sched_elect();
    if (unlikely(mgr_task_get_sp(next, &next_frame) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
err_autotest:
#ifdef CONFIG_BUILD_TARGET_AUTOTEST
    /* autotest special case: if sending to itself, set current as ready,
     * no schedule neither elect has been made
     */
    if (unlikely(current == target)) {
        mgr_task_set_sysreturn(current, STATUS_OK);
    }
#endif
err:
    return next_frame;
}
