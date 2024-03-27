#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/time.h>
#include <sentry/arch/asm-generic/panic.h>
#include <uapi/types.h>
#include <sentry/sched.h>

stack_frame_t *gate_alarm(stack_frame_t *frame, uint32_t delay_ms, bool periodic)
{
    taskh_t current = sched_get_current();
    taskh_t next;
    stack_frame_t *next_frame = frame;

    if (unlikely(mgr_time_delay_add_signal(current, delay_ms, SIGNAL_ALARM, periodic) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_BUSY);
        goto end;
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
}
