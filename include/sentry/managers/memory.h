// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef MEMORY_MANAGER_H
#define MEMORY_MANAGER_H

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
    MM_REGION_KERNEL_TXT,
    MM_REGION_KERNEL_DATA,
    MM_REGION_KERNEL_DEVICE,
#if defined(__arm__)
    MM_REGION_KERNEL_SYSARM,
#endif
    MM_REGION_TASK_SVC_EXCHANGE,
    MM_REGION_TASK_TXT,
    MM_REGION_TASK_DATA,
    MM_REGION_TASK_DEVICE,
    MM_REGION_TASK_SHM,
} mm_region_t;

stack_frame_t *memfault_handler(stack_frame_t *frame);

kstatus_t mgr_mm_map(mm_region_t reg_type, uint32_t reg_handle, taskh_t requester);

kstatus_t mgr_mm_ummap(mm_region_t reg_type, uint32_t reg_handle, taskh_t requester);

kstatus_t mgr_mm_init(void);

kstatus_t mgr_mm_watchdog(void);


#endif/*!MEMORY_MANAGER_H*/
