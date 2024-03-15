#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/device.h>
#include <sentry/sched.h>
#include <sentry/arch/asm-generic/panic.h>

stack_frame_t *gate_exit(const stack_frame_t *frame, uint32_t result)
{
    taskh_t current = sched_get_current();
    taskh_t next;
    stack_frame_t *next_frame = NULL;

    if (unlikely(mgr_task_set_jobreturn(current, result) != K_STATUS_OKAY)) {
        /* should never fail! */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    /* it is (communaly) admitted that 'return 0' is a standard successful return */
    if (unlikely(result != 0)) {
        if (unlikely(mgr_task_set_state(current, JOB_STATE_ABORTING) != K_STATUS_OKAY)) {
            panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
        }
    } else {
        if (unlikely(mgr_task_set_state(current, JOB_STATE_FINISHED) != K_STATUS_OKAY)) {
            panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
        }
    }
    /* no syscall return code here, as the job is **never** reelected.
     * in order to ensure that such reelection do not happen, the task syscall return
     * code value is set to NON_SENSE, generating a voluntary panic() if elected again
     */
    mgr_task_set_sysreturn(current, STATUS_NON_SENSE);
    /* now electing a new job, sched_elect() never fails */
    next = sched_elect();
    if (unlikely(mgr_task_get_sp(next, &next_frame) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    return next_frame;
}
