#include <sentry/syscalls.h>
#include <uapi/types.h>
#include <sentry/managers/memory.h>
#include <sentry/sched.h>

stack_frame_t *gate_shm_setcreds(stack_frame_t *frame, shmh_t shm, taskh_t target, SHMPermission perms)
{
    taskh_t current = sched_get_current();
    shmh_t shmhandle;
    shm_user_t user;
    shm_config_t config;

    if (unlikely(mgr_mm_shm_get_task_type(shm, current, &user) != K_STATUS_OKAY)) {
        /* smoke test here, this branch should never happen */
        /*@ assert(false); */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* is target exists ? */
    if (unlikely(mgr_task_handle_exists(target) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(user == SHM_TSK_NONE)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(user == SHM_TSK_USER)) {
        /* only owner can set SHM creds */
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    /*@ assert (user == SHM_TSK_OWNER); */
    config.rw = SECURE_FALSE;
    config.transferable = SECURE_FALSE;
    if (perms | SHM_PERMISSION_WRITE) {
        config.rw = SECURE_TRUE;
    }
    if (perms | SHM_PERMISSION_TRANSFER) {
        config.transferable = SECURE_TRUE;
    }
    if (target == current) {
        /* settings own perms */
        mgr_mm_shm_configure(shm, SHM_TSK_OWNER, &config);
    } else {
        mgr_mm_shm_declare_user(shm, target);
        mgr_mm_shm_configure(shm, SHM_TSK_USER, &config);
    }
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}
