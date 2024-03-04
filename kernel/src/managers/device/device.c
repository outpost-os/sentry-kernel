// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file device list manipulation API implementation
 *
 * This file is the lonely file including the devlist-dt header
 * to avoid memory duplication.
 */
#include <assert.h>
#include <string.h>
#include <sentry/ktypes.h>
#include <sentry/managers/device.h>
#include <sentry/managers/task.h>

#include "devlist-dt.h"

/**
 * This structure hold dynamic informations that is forged at init time.
 * While device_t table is a const informations list, that one hold dynamic content
 * used in order to keep, for each subjet (kernel, task), the state of the corresponding
 * device.
 */
typedef struct device_state {
    const device_t  *device;
    secure_bool_t    mapped;
    /** XXX: released can be considered, if we consider the action of definitely releasing a device */
    taskh_t          owner;
} device_state_t;

device_state_t devices_state[DEVICE_LIST_SIZE];

/**
 * @brief return a device metadata structure based on a device handle
 */
static inline const device_t *mgr_device_get_device(devh_t d)
{
    const device_t *dev = NULL;
    /* here we do not match only the id but also the capability and family
     * (i.e. full opaque check)
     */
    for (uint32_t i = 0; i < DEVICE_LIST_SIZE; ++i) {
        const devh_t handle = forge_devh(devices_state[i].device);
        if (handle == d) {
            dev = &devices[i];
            break;
        }
    }
    return dev;
}

/**
 * @brief initialize the device manager
 *
 * At startup, no device is mapped except ARM SCS block for kernel (NVIC, Systick).
 * This do not requires start this manager before any device manipulation (while
 * memory protection is not yet set). But when executing this function, the kernel
 * consider that no kernel device is mapped (mapped flag setting).
 * Although it requires tasks to be ready and thus,
 * task init to be executed:
 * platform_init (ARM SCS) <- sched_init <- mgr_task_init <- mgr_device_init
 * then all other managers that manipulate BSP can be executed
 */
kstatus_t mgr_device_init(void)
{
    kstatus_t status = K_STATUS_OKAY;
    taskh_t owner = 0;
    taskh_t owner_from_metadata = 0;
    devh_t  devh;

    memset(devices_state, 0x0, DEVICE_LIST_SIZE*sizeof(device_state_t));
    /*
     * let's boot strap the devices list.
     */
    for (uint32_t i = 0; i < DEVICE_LIST_SIZE; ++i) {
        devices_state[i].device = &devices[i];
        devices_state[i].mapped = SECURE_FALSE;
        /* in order to speed-up ownership of device, the effective taskh handle
         * of the ownering task is set at init time.
         * the owner is get back from the task manager, to ensure an effective
         * association between the device owner in the dts and the one of the
         * metadata.
         * To do this, we:
         * - get back the taskh_t using the dts 'outpost,owner' label
         * - we check that this owner (using the handle) do matches the metadata,
         *   by asking the task manager to confirm.
         *
         * As all this work is done once for all at init time, it do not
         * impact runtime performances.
         */
        if (mgr_task_get_handle(devices[i].owner, &owner) != K_STATUS_OKAY) {
            /* owner is not a task */
            owner = 0;
        } else {
            devh = forge_devh(devices_state[i].device);
            if (unlikely(mgr_task_get_device_owner(devh, &owner_from_metadata) != K_STATUS_OKAY)) {
                panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
            }
            if (unlikely(owner_from_metadata != owner)) {
                /* dts owner do not match the metadata owner !
                 * This is a configuration mismatch !
                 */
                panic(PANIC_CONFIGURATION_MISMATCH);
            }
        }
        /* adding taskh value (0 or effective taskh userspace handle) */
        devices_state[i].owner = owner;
    }
    return status;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_device_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif

kstatus_t mgr_device_watchdog(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}

/**
 * @brief return SECURE_TRUE of the dev handle do exists
 */
secure_bool_t mgr_device_exists(devh_t d)
{
    secure_bool_t res = SECURE_FALSE;
    if (mgr_device_get_device(d) != NULL) {
        res = SECURE_TRUE;
    }
    return res;
}

/**
 * @brief return the userspace part (devinfo_t) of a device, using dev handle
 */
kstatus_t mgr_device_get_info(devh_t d, const devinfo_t **devinfo)
{
    kstatus_t status = K_ERROR_INVPARAM;

    if (unlikely(devinfo == NULL)) {
        goto end;
    }
    for (uint32_t i = 0; i < DEVICE_LIST_SIZE; ++i) {
        const devh_t handle = forge_devh(devices_state[i].device);
        if (handle == d) {
                *devinfo = &devices_state[i].device->devinfo;
                status = K_STATUS_OKAY;
                goto end;
        }
    }
    status = K_ERROR_NOENT;
end:
    return status;
}

/**
 * @brief return SECURE_TRUE if the device is a kernel device
 */
secure_bool_t mgr_device_is_kernel(devh_t d)
{
    secure_bool_t res = SECURE_TRUE;

    for (uint32_t i = 0; i < DEVICE_LIST_SIZE; ++i) {
        const devh_t handle = forge_devh(devices_state[i].device);
        if (handle == d) {
                if (devices_state[i].owner == 0x0UL) {
                    res = SECURE_FALSE;
                }
                goto end;
        }
    }
end:
    return res;
}

/**
 * @brief return the device owner (taskh_t) for given device
 *
 * @param[in] d: device handle for which the request is done
 * @param[out] owner: the owner to be set
 *
 * @returns
 *   K_ERROR_INVPARAM if owner is NUL
 *   K_ERROR_NOENT if device is not found
 *   K_STATUS_OK if the device owner is found
 */
kstatus_t mgr_device_get_owner(devh_t d, taskh_t *owner)
{
    kstatus_t status = K_ERROR_NOENT;

    if (unlikely(owner == NULL)) {
        status = K_ERROR_INVPARAM;
        goto end;
    }
    /*@ assert \valid(owner); */
    for (uint32_t i = 0; i < DEVICE_LIST_SIZE; ++i) {
        const devh_t handle = forge_devh(devices_state[i].device);
        if (handle == d) {
                *owner = devices_state[i].owner;
                status = K_STATUS_OKAY;
                goto end;
        }
    }
    /*@ assert(status == K_ERROR_NOENT); */
end:
    return status;
}

/**
 * @brief return the device handle (devh_t) for given device
 *
 * @param[in] dev_label: device identifier, shared with userspace
 * @param[out] devhandle: the effective device handle
 *
 * @returns
 *   K_ERROR_INVPARAM if devhandle is NULL
 *   K_STATUS_OK if the device handle has been forged and returned
 */
kstatus_t mgr_device_get_devhandle(uint32_t dev_label, devh_t *devhandle)
{
    kstatus_t status = K_ERROR_NOENT;

    if (unlikely(devhandle == NULL)) {
        status = K_ERROR_INVPARAM;
        goto end;
    }
    /*@ assert \valid(devhandle); */
    if (unlikely(dev_label >= DEVICE_LIST_SIZE)) {
        status = K_ERROR_INVPARAM;
        goto end;
    }
    *devhandle = forge_devh(devices_state[dev_label].device);
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief get back device clock config (bus identifier and clock identifier)
 *
 * @param[in] d: device handler, unique to the system
 * @param[out] clk_id: device clk identifier to set
 * @param[out] bus_id: device bus identifier to set
 */
kstatus_t mgr_device_get_clock_config(const devh_t d, uint32_t *clk_id, uint32_t *bus_id)
{
    kstatus_t status = K_ERROR_NOENT;

    if (unlikely(clk_id == NULL || bus_id == NULL)) {
        status = K_ERROR_INVPARAM;
        goto end;
    }
    /*@ assert \valid(clk_id); */
    /*@ assert \valid(bus_id); */
    for (uint32_t i = 0; i < DEVICE_LIST_SIZE; ++i) {
        const devh_t handle = forge_devh(devices_state[i].device);
        if (handle == d) {
                *clk_id = devices_state[i].device->clk_id;
                *bus_id = devices_state[i].device->bus_id;
                status = K_STATUS_OKAY;
                goto end;
        }
    }
end:
    return status;
}

uint32_t mgr_device_get_capa(devh_t d)
{
    uint32_t capa = 0;

    for (uint32_t i = 0; i < DEVICE_LIST_SIZE; ++i) {
        const devh_t handle = forge_devh(devices_state[i].device);
        if (handle == d) {
                capa =  devices_state[i].device->capability & CAP_DEV_MASK;
                goto end;
        }
    }
end:
    return capa;
}

kstatus_t mgr_device_walk(const devinfo_t **devinfo, uint8_t id)
{
    kstatus_t status = K_ERROR_INVPARAM;

    if (unlikely(devinfo == NULL)) {
        goto end;
    }
    if (unlikely(id >= DEVICE_LIST_SIZE)) {
        *devinfo = NULL;
        status = K_ERROR_NOENT;
        goto end;
    }
    *devinfo = &devices[id].devinfo;
    status = K_STATUS_OKAY;
end:
    return status;
}

static inline secure_bool_t dev_has_interrupt(const devinfo_t *devinfo, uint8_t IRQn)
{
    secure_bool_t res = SECURE_FALSE;

    if (unlikely(devinfo->num_interrupt == 0)) {
        goto end;
    }
    for (uint8_t i = 0; i < devinfo->num_interrupt; ++i) {
        if (devinfo->its[i].it_num == IRQn) {
            res = SECURE_TRUE;
            goto end;
        }
    }
end:
    return res;
}

kstatus_t mgr_device_get_devh_from_interrupt(uint8_t IRQn, devh_t *devh)
{
    kstatus_t status = K_ERROR_INVPARAM;

    if (unlikely(devh == NULL)) {
        goto end;
    }
    for (uint32_t i = 0; i < DEVICE_LIST_SIZE; ++i) {
        if (dev_has_interrupt(&devices_state[i].device->devinfo, IRQn) == SECURE_TRUE) {
            const devh_t handle = forge_devh(devices_state[i].device);
            *devh = handle;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
    status = K_ERROR_NOENT;
end:
    return status;
}

kstatus_t mgr_device_get_devinfo_from_interrupt(uint8_t IRQn, const devinfo_t **devinfo)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(devinfo == NULL)) {
        goto end;
    }
    for (uint32_t i = 0; i < DEVICE_LIST_SIZE; ++i) {
        if (dev_has_interrupt(&devices_state[i].device->devinfo, IRQn) == SECURE_TRUE) {
            *devinfo = &devices_state[i].device->devinfo;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
    status = K_ERROR_NOENT;
end:
    return status;
}
