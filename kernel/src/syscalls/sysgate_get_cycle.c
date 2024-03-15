#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/security.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/arch/asm-generic/tick.h>
#include <sentry/sched.h>

stack_frame_t *gate_get_cycle(stack_frame_t *frame, uint32_t precision)
{
    taskh_t current = sched_get_current();
    stack_frame_t *next_frame = frame;
    taskh_t job_handle;
    const task_meta_t *meta;
    uint64_t *svcexch;

    if (unlikely(precision > PRECISION_MILLISECONDS)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(precision < PRECISION_NANOSECONDS)) {
        if (unlikely(mgr_security_has_capa(current, CAP_TIM_HP_CHRONO) != SECURE_TRUE)) {
            mgr_task_set_sysreturn(current, STATUS_DENIED);
            goto end;
        }
    }
    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    svcexch = (uint64_t*)meta->s_svcexchange;
    switch (precision) {
        case PRECISION_CYCLE:
            svcexch[0] = systime_get_cycle();
            break;
        case PRECISION_NANOSECONDS:
            svcexch[0] = systime_get_nanoseconds();
            break;
        case PRECISION_MICROSECONDS:
            svcexch[0] = systime_get_microseconds();
            break;
        case PRECISION_MILLISECONDS:
            svcexch[0] = systime_get_milliseconds();
            break;
        default:
            panic(PANIC_UNEXPECTED_BRANCH_EXEC);
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
}
