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
#if defined(__arm__)
    MM_REGION_KERNEL_SYSARM,
#endif
    MM_REGION_TASK_SVC_EXCHANGE,
    MM_REGION_TASK_TXT,
    MM_REGION_TASK_DATA,
    MM_REGION_TASK_DEVICE,
    MM_REGION_TASK_SHM,
} mm_region_t;

#if defined(CONFIG_HAS_MPU_PMSA_V7)
typedef struct __attribute__((packed)) region_config {
    uint32_t rbar;
    uint32_t rsar;
} region_config_t;

/**
 * @brief ARMv7M MPU RBAR/RSAR register pair pool, for fast storage
 */
typedef struct __attribute__((packed)) ressource_config {
    region_config_t region[4];
} ressource_config_t;
#endif

stack_frame_t *memfault_handler(stack_frame_t *frame);

kstatus_t mgr_mm_map(mm_region_t reg_type, uint32_t reg_handle, taskh_t requester);

kstatus_t mgr_mm_unmap(mm_region_t reg_type, uint32_t reg_handle, taskh_t requester);

kstatus_t mgr_mm_init(void);

kstatus_t mgr_mm_watchdog(void);

/* BSP related, not for syscalls */
kstatus_t mgr_mm_map_kdev(uint32_t address, size_t len);

kstatus_t mgr_mm_unmap_kdev(void);

#endif/*!MEMORY_MANAGER_H*/
