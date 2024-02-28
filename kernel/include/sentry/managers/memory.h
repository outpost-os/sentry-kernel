// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef MEMORY_MANAGER_H
#define MEMORY_MANAGER_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <sentry/arch/asm-generic/memory.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/managers/task.h>

/**
 * This enumerate defines the contigous memory regions that
 * can be (un)mapped by the memory manager.
 * All these regions are associated to a set of permissions
 * automatically, and their addresses are the consequence of
 *    - the current layout/task being executed for most of them (except shm and device)
 *    - the handle passed in 2nd argument (task handle, shm handle, device handle) for some
 *      of them
 */
typedef enum mm_region {
    MM_REGION_TASK_TXT = TASK_FIRST_REGION_NUMBER, /* starting point of userspace ressources */
    MM_REGION_TASK_DATA = TASK_FIRST_REGION_NUMBER + 1,
    MM_REGION_TASK_RESSOURCE_DEVICE, /* starting at 4, no fixed order */
    MM_REGION_TASK_RESSOURCE_SHM,
} mm_region_t;

typedef enum mm_k_region {
    MM_REGION_KERNEL_TXT = 0, /* starting point of userspace ressources */
    MM_REGION_KERNEL_DATA = 1,
    MM_REGION_KERNEL_DEVICE = CONFIG_NUM_MPU_REGIONS - 1,
} mm_k_region_t;

kstatus_t mgr_mm_resize_taskdata_to_svcexchange(taskh_t target);

kstatus_t mgr_mm_init(void);

kstatus_t mgr_mm_watchdog(void);

/* BSP related, not for syscalls */
kstatus_t mgr_mm_map_kdev(uint32_t address, size_t len);

kstatus_t mgr_mm_unmap_kdev(void);

/* kernel case only: map another task than current svc echange area to
 * allow single-copy of exchange data between tasks
 */
kstatus_t mgr_mm_map_svcexchange(taskh_t t);

kstatus_t mgr_mm_forge_empty_table(layout_resource_t *ressource_tab);

/* fast implementation of task mapping.
   map all task currently mapped ressources. all empty user regions are cleared
*/
kstatus_t mgr_mm_map_task(taskh_t t);

/**
 * Map a device into the associated task owner layout
 *
 * Do **not** handle I/O nor interrupts neither clock config
 * (see corresponding managers for this)
 */
kstatus_t mgr_mm_map_device(devh_t dev);

/**
 * unmap a previously mapped device from the associated task owner layout
 */
kstatus_t mgr_mm_unmap_device(devh_t dev);


kstatus_t mgr_mm_forge_ressource(mm_region_t reg_type, taskh_t t, layout_resource_t *ressource);

/*
 * XXX:
 *  In order to restore task mpu config w/ fast loading, region configuration
 *  in task layout must be ordered **and** contiguous. So, use these helper
 *  as this is not related to mpu driver but memory management.
 */

/**
 * @brief convert a MPU region ID to a task layout region ID
 *
 * @param  region_id MPU region id
 * @return The associated id in task layout table.
 */
static inline uint8_t mm_mgr_region_to_layout_id(uint8_t region_id)
{
    if (unlikely(region_id >= CONFIG_NUM_MPU_REGIONS)) {
        panic(PANIC_HARDWARE_INVALID_STATE); /* TODO: do we add a BUG panic event as in linux ? */
    }
    return region_id - TASK_FIRST_REGION_NUMBER;
}

static inline uint8_t mm_mgr_layout_to_region_id(uint8_t layout_id)
{
    if (unlikely(layout_id >= TASK_MAX_RESSOURCES_NUM)) {
        panic(PANIC_HARDWARE_INVALID_STATE); /* TODO: do we add a BUG panic event as in linux ? */
    }
    return layout_id + TASK_FIRST_REGION_NUMBER;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_mm_autotest(void);
#endif

#if defined(__cplusplus)
}
#endif

#endif/*!MEMORY_MANAGER_H*/
