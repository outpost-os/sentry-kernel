#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/sched.h>
#include <uapi/types.h>

stack_frame_t *gate_send_signal(stack_frame_t *frame,
                                taskh_t       target,
                                uint32_t      signal)

{
    taskh_t current = sched_get_current();
    kstatus_t status;
#ifndef CONFIG_BUILD_TARGET_AUTOTEST
    if (unlikely(current == target)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
#endif
    if (unlikely(signal < SIGNAL_ABORT || signal > SIGNAL_USR2)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    status = mgr_task_push_sig_event(signal, current, target);
    if (unlikely(status == K_ERROR_INVPARAM)) {
        /* target not found */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(status == K_ERROR_BUSY)) {
        /* target signal slot for us is already fullfill */
        mgr_task_set_sysreturn(current, STATUS_BUSY);
        goto end;
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}
