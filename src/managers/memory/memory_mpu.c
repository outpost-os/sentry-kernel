// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry memory manager implementation
 */
#include <inttypes.h>
#include <sentry/arch/asm-cortex-m/mpu.h>
#include <sentry/arch/asm-generic/membarriers.h>
#include <sentry/managers/debug.h>
#include <sentry/managers/memory.h>

extern uint32_t _svtor;
extern uint32_t _ram_start;

struct mpu_region_desc kernel_mem_config[] = {
    /* kernel txt */
    {
        .id = 0,
        .addr = (uint32_t)&_svtor, /* starting at vtor for ^2 size vs base alignment */
        .size = MPU_REGION_SIZE_32KB,
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
        .mask = 0x0,
        .noexec = false,
    },
    /* kernel data */
    {
        .id = 1,
        .addr = (uint32_t)&_ram_start,
        .size = MPU_REGION_SIZE_16KB, /* ldscript to fix, this is big */
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
        .mask = 0x0,
        .noexec = true,
    },
    /* system memory, strongly ordered */
    {
        .id = 2,
        .addr = SCS_BASE,
        .size = MPU_REGION_SIZE_1MB,
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_STRONGLY_ORDER,
        .mask = 0x0,
        .noexec = true,
    },
    /* ST devices */
    {
        .id = 3,
        .addr = 0x40000000UL, /* layout base addr, to generate in layout.h */
        .size = MPU_REGION_SIZE_256MB, /* layout size to generate in layout.h, or Kdevices to map separately */
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_STRONGLY_ORDER,
        .mask = 0x0,
        .noexec = true,
    },
};

/*
 * Per region function implementation, forced inline, but
 * clearer.
 */

__STATIC_INLINE kstatus_t mgr_mm_map_kernel_txt(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}

__STATIC_INLINE kstatus_t mgr_mm_map_kernel_data(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}

__STATIC_INLINE kstatus_t mgr_mm_map_kernel_devices(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}



kstatus_t mgr_mm_map(mm_region_t regid, uint32_t handle)
{
    kstatus_t status = K_SECURITY_INTEGRITY;
    switch (regid) {
        case MM_REGION_KERNEL_TXT:
            status = mgr_mm_map_kernel_txt();
            break;
        case MM_REGION_KERNEL_DATA:
            status = mgr_mm_map_kernel_data();
            break;
        case MM_REGION_KERNEL_DEVICES:
            status = mgr_mm_map_kernel_devices();
            break;
        case MM_REGION_TASK_SVC_EXCHANGE:
            break;
        case MM_REGION_TASK_TXT:
            break;
        case MM_REGION_TASK_DATA:
            break;
        case MM_REGION_TASK_DEVICE:
            break;
        case MM_REGION_TASK_SHM:
            break;
        default:
            goto end;
    }
end:
    return status;
}

kstatus_t mgr_mm_unmap(mm_region_t regid, uint32_t handle)
{
    kstatus_t status = K_SECURITY_INTEGRITY;
    return status;
}


kstatus_t mgr_mm_init(void)
{
    kstatus_t status = K_STATUS_OKAY;
#ifdef CONFIG_HAS_MPU
    mpu_disable();
    status = mpu_load_configuration(kernel_mem_config, ARRAY_SIZE(kernel_mem_config));
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }
    mpu_enable();
end:
#endif
    return status;
}


kstatus_t mgr_mm_watchdog(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
