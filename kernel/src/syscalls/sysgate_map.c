#include <uapi/uapi.h>
#include <sentry/syscalls.h>
#include <sentry/managers/interrupt.h>
#include <sentry/managers/memory.h>
#include <sentry/managers/task.h>
#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/sched.h>

/**
 * @fn gate_map_dev - Map a device in current task layout
 *
 * @param[in] frame current job's frame. Not updated here
 * @param[in] device device handle to map
 *
 * @return current job frame (no modification)
 */
stack_frame_t *gate_map_dev(stack_frame_t *frame, devh_t device)
{
    taskh_t current = sched_get_current();
    taskh_t task;
    uint32_t capa;
    secure_bool_t is_mapped;
    secure_bool_t is_configured;

    if (unlikely(mgr_device_get_owner(device, &task) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* device is valid */
#ifndef CONFIG_BUILD_TARGET_DEBUG // FIXME: need tooling update
    if (unlikely(current != task)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely((capa = mgr_device_get_capa(device)) == 0)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (unlikely(mgr_security_has_capa(current, capa) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
#endif
    /* current task own the device and has capa to use it */

    if (mgr_device_get_map_state(device, &is_mapped) != K_STATUS_OKAY) {
        /* should not happen with a valid device */
        /*@ assert \false; */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (unlikely(is_mapped != SECURE_FALSE)) {
        /* invstate ? */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (mgr_device_get_configured_state(device, &is_configured) != K_STATUS_OKAY) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (likely(is_configured == SECURE_FALSE)) {
        mgr_device_configure(device);
    }
    if (unlikely(mgr_mm_map_device(current, device) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_BUSY);
        goto end;
    }
    mgr_device_set_map_state(device, SECURE_TRUE);
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}


stack_frame_t *gate_unmap_dev(stack_frame_t *frame, devh_t device)
{
    taskh_t current = sched_get_current();
    taskh_t task;
    uint32_t capa;
    secure_bool_t is_mapped;

    if (unlikely(mgr_device_get_owner(device, &task) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
#ifndef CONFIG_BUILD_TARGET_DEBUG // FIXME: need tooling update
    /* device is valid */
    if (unlikely(current != task)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely((capa = mgr_device_get_capa(device)) == 0)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (unlikely(mgr_security_has_capa(current, capa) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
#endif
    /* current task own the device and has capa to use it */

    if (mgr_device_get_map_state(device, &is_mapped) != K_STATUS_OKAY) {
        /* should not happen with a valid device */
        /*@ assert \false; */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (unlikely(is_mapped != SECURE_TRUE)) {
        /* invstate ? */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_mm_unmap_device(current, device) != K_STATUS_OKAY)) {
        /* should not happen with a valid, mapped and owned device */
        /*@ assert \false; */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    mgr_device_set_map_state(device, SECURE_FALSE);
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return frame;
}
