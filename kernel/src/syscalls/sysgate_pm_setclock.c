#include <uapi/uapi.h>
#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/clock.h>
#include <sentry/managers/security.h>
#include <sentry/sched.h>

stack_frame_t *gate_pm_clock_set(stack_frame_t *frame, uint32_t clk_reg, uint32_t clkmsk, uint32_t val)
{
    stack_frame_t *next_frame = frame;
    taskh_t current = sched_get_current();

    if (unlikely(mgr_security_has_capa(current, CAP_SYS_POWER) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(mgr_clock_configure_clockline(clk_reg, clkmsk, val) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
}
