#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/time.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/sched.h>
#include <uapi/types.h>

stack_frame_t *gate_sleep(stack_frame_t *frame, uint32_t duration_ms, uint32_t sleep_mode)
{
    taskh_t current = sched_get_current();
    stack_frame_t *next_frame = frame;
    taskh_t next;
    const task_meta_t *meta;
    taskh_t *svcexch;
    kstatus_t res;

    if (unlikely(sleep_mode > SLEEP_MODE_DEEP)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_time_delay_add_job(current, duration_ms) != K_STATUS_OKAY)) {
        /* TODO: define if the sleep() failure is considered as a panic event or not */
        mgr_task_set_sysreturn(current, STATUS_BUSY);
        goto end;
    }
    if (sleep_mode == SLEEP_MODE_DEEP) {
        res = mgr_task_set_state(current, JOB_STATE_SLEEPING_DEEP);
    } else {
        res = mgr_task_set_state(current, JOB_STATE_SLEEPING);
    }
    if (unlikely(res != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    /* the job return code must be updated by the delay manager or any awokening event,
     * and thus these source events must update the syscall return code when making
     * this job eligible again to scheduling.
     * By default, if this behavior is not respected, the kernel will panic at job
     * job election time.
     */
    mgr_task_set_sysreturn(current, STATUS_NON_SENSE);
    next = sched_elect();
    if (unlikely(mgr_task_get_sp(next, &next_frame) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
end:
    return next_frame;
}
