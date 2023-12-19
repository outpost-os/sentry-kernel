// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef MEMORY_MANAGER_H
#define MEMORY_MANAGER_H

#if defined(__cplusplus)
extern "C" {
#endif

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
    MM_REGION_TASK_TXT = 2, /* starting point of userspace ressources */
    MM_REGION_TASK_DATA = 3,
    MM_REGION_TASK_RESSOURCE = 4, /* starting at 4 */
} mm_region_t;

typedef enum mm_k_region {
    MM_REGION_KERNEL_TXT = 0, /* starting point of userspace ressources */
    MM_REGION_KERNEL_DATA = 1,
    MM_REGION_KERNEL_DEVICE = 7,
} mm_k_region_t;

kstatus_t mgr_mm_map(mm_region_t reg_type, uint32_t reg_handle, taskh_t requester);

kstatus_t mgr_mm_unmap(mm_region_t reg_type, uint32_t reg_handle, taskh_t requester);

kstatus_t mgr_mm_resize_taskdata_to_svcexchange(taskh_t target);

kstatus_t mgr_mm_init(void);

kstatus_t mgr_mm_watchdog(void);

/* BSP related, not for syscalls */
kstatus_t mgr_mm_map_kdev(uint32_t address, size_t len);

kstatus_t mgr_mm_unmap_kdev(void);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_mm_autotest(void);
#endif

#if defined(__cplusplus)
}
#endif

#endif/*!MEMORY_MANAGER_H*/
