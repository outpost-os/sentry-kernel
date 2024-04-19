#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/security.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/arch/asm-generic/tick.h>
#include <sentry/sched.h>

stack_frame_t *gate_log(stack_frame_t *frame, __MAYBE_UNUSED uint32_t log_len)
{
#if CONFIG_BUILD_TARGET_RELEASE
    taskh_t current = sched_get_current();

    mgr_task_set_sysreturn(current, STATUS_OK);
    return frame;
#else
    taskh_t current = sched_get_current();
    stack_frame_t *next_frame = frame;
    taskh_t job_handle;
    const task_meta_t *meta;
    uint8_t *svcexch;

    if (unlikely(log_len > CONFIG_SVC_EXCHANGE_AREA_LEN)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    svcexch = (uint8_t*)meta->s_svcexchange;
    debug_rawlog(svcexch, log_len);
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
#endif
}
