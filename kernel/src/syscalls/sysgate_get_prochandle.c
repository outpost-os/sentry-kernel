#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/sched.h>

stack_frame_t *gate_get_prochandle(stack_frame_t *frame, uint32_t job_label)
{
    taskh_t current = sched_get_current();
    stack_frame_t *next_frame = frame;
    taskh_t job_handle;
    const task_meta_t *meta;
    taskh_t *svcexch;

    if (unlikely(mgr_task_get_handle(job_label, &job_handle) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* set taskh_t value into svcexchange */
    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    svcexch = (uint32_t*)meta->s_svcexchange;
    svcexch[0] = job_handle;
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
}
