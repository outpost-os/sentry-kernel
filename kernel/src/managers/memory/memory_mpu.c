// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry memory manager implementation
 */
#include <inttypes.h>

#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-generic/membarriers.h>
#include <sentry/arch/asm-generic/panic.h>


#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/arch/asm-cortex-m/mpu.h>
#include <sentry/arch/asm-cortex-m/handler.h>
#elif defined(__x86_64__)
// TODO add core,mmu and handler headers (or minimum to compile)
#elif defined(__i386__)
// TODO add core,mmu and handler headers (or minimum to compile)
#else
#error "unsupported architecture!"
#endif

#include <sentry/managers/debug.h>
#include <sentry/managers/task.h>
#include <uapi/handle.h>

#include <sentry/managers/memory.h>

extern uint32_t _svtor;
extern uint32_t _ram_start;

static secure_bool_t mm_configured;

static inline secure_bool_t mgr_mm_configured(void)
{
    if (mm_configured == SECURE_TRUE) {
        return mm_configured;
    }
    return SECURE_FALSE;
}

/*
 * Per region function implementation, forced inline, but
 * clearer.
 */

__STATIC_INLINE kstatus_t mgr_mm_map_kernel_txt(void)
{
    kstatus_t status = K_STATUS_OKAY;
    struct mpu_region_desc kernel_txt_config = {
        .id = MM_REGION_KERNEL_TXT,
        .addr = (uint32_t)&_svtor, /* starting at vtor for ^2 size vs base alignment */
        .size = MPU_REGION_SIZE_32KB,
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
        .mask = 0x0,
        .noexec = false,
    };
    status = mpu_load_configuration(&kernel_txt_config, 1);
    return status;
}

__STATIC_INLINE kstatus_t mgr_mm_map_kernel_data(void)
{
    kstatus_t status = K_STATUS_OKAY;
    struct mpu_region_desc kernel_data_config = {
        .id = MM_REGION_KERNEL_DATA,
        .addr = (uint32_t)&_ram_start,
        .size = MPU_REGION_SIZE_16KB, /* ldscript to fix, this is big */
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
        .mask = 0x0,
        .noexec = true,
    };
    status = mpu_load_configuration(&kernel_data_config, 1);
    return status;
}

/**
 * Reduce current data section to svcexchange only
 * INFO: optimisation can be done here: MPU register states should be cached in task data to avoid dyn calculation
 */
kstatus_t mgr_mm_resize_taskdata_to_svcexchange(taskh_t target)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_meta_t const * meta;
    if (unlikely((status = mgr_task_get_metadata(target, &meta)) == K_ERROR_INVPARAM)) {
        /* invalid task handle */
        pr_err("failed to get metadata for task %08x",
        handle_convert_to_u32(target));
        goto err;
    }
    struct mpu_region_desc user_data_config = {
        .id = MM_REGION_TASK_DATA,
        .addr = (uint32_t)meta->s_svcexchange, /* To define: where start the task RAM ? .data ? other ? */
        .size = mpu_convert_size_to_region(CONFIG_SVC_EXCHANGE_AREA_LEN),
        .access_perm = MPU_REGION_PERM_FULL,
        .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
        .mask = 0x0,
        .noexec = true,
    };
    status = mpu_load_configuration(&user_data_config, 1);
err:
    return status;
}



kstatus_t mgr_mm_map_task(taskh_t t)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const layout_ressource_t *layout;
    if (unlikely((status = mgr_task_get_layout_from_handle(t, &layout)) != K_STATUS_OKAY)) {
        pr_err("failed to get meta for task handle %x", t);
        goto err;
    }
    mpu_fastload(layout, CONFIG_NUM_MPU_REGIONS-2);
    status = K_STATUS_OKAY;
err:
    return status;
}

/**
 * @brief forge an empty task memory layout
 *
 * all task memory regions are set as invalid
 */
kstatus_t mgr_mm_forge_empty_table(layout_ressource_t *ressource_tab)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(ressource_tab == NULL)) {
        goto err;
    }
    for (uint8_t i = 0; i < CONFIG_NUM_MPU_REGIONS-2;++i) {
        mpu_forge_unmapped_ressource(i + MM_REGION_TASK_TXT, ressource_tab);
        ressource_tab++;
    }
    status = K_STATUS_OKAY;
err:
    return status;
}

/**
 * @brief forge a ressource opaque entry for the entry layout table
 *
 * all task memory regions are set as invalid
 */
kstatus_t mgr_mm_forge_ressource(mm_region_t reg_type, taskh_t t, layout_ressource_t *ressource)
{
    kstatus_t status = K_SECURITY_INTEGRITY;
    const task_meta_t *meta;
    struct mpu_region_desc mpu_cfg;
    if (unlikely((status = mgr_task_get_metadata(t, &meta)) == K_ERROR_INVPARAM)) {
        /* invalid task handle */
        pr_err("failed to get metadata for task %08x",
        handle_convert_to_u32(t));
        goto err;
    }
    switch (reg_type) {
        case MM_REGION_TASK_TXT:
            mpu_cfg.id = MM_REGION_TASK_TXT,
            mpu_cfg.addr = (uint32_t)meta->s_text,
            mpu_cfg.size = mpu_convert_size_to_region(mgr_task_get_text_region_size(meta)),
            mpu_cfg.access_perm = MPU_REGION_PERM_RO,
            mpu_cfg.access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
            mpu_cfg.mask = 0x0,
            mpu_cfg.noexec = false,
            mpu_forge_ressource(&mpu_cfg, ressource);
            break;
        case MM_REGION_TASK_DATA:
            mpu_cfg.id = MM_REGION_TASK_DATA,
            mpu_cfg.addr = (uint32_t)meta->s_svcexchange, /* To define: where start the task RAM ? .data ? other ? */
            mpu_cfg.size = mpu_convert_size_to_region(mgr_task_get_data_region_size(meta)),   /* FIXME data_size is a concat of all datas sections */
            mpu_cfg.access_perm = MPU_REGION_PERM_FULL,
            mpu_cfg.access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
            mpu_cfg.mask = 0x0,
            mpu_cfg.noexec = true,
            mpu_forge_ressource(&mpu_cfg, ressource);
            break;
        case MM_REGION_TASK_RESSOURCE_DEVICE:
            /* TODO for other ressources */
            break;
        case MM_REGION_TASK_RESSOURCE_SHM:
            /* TODO for other ressources */
            break;
        default:
            break;
    }
    status = K_STATUS_OKAY;
err:
    return status;
}

/*
 * @brief initialize MPU and configure kernel layout
 *
 * layout is the following:
 *
 * In kernel mode (syscalls):
 *                                                     S     U
 * [MPU REG 0] [ kernel TXT section                ] [R-X] [---]
 * [MPU REG 1] [ kernel DATA section               ] [RW-] [---]
 * [MPU REG 2] [ kernel current device, if needed  ] |RW-] [---] SO
 * [MPU REG 3] [ task Data SVC-exchange region     ] [RW-] [RW-]
 * [MPU REG 4] [                                   ] [---] [---]
 * [MPU REG 5] [                                   ] [---] [---]
 * [MPU REG 6] [                                   ] [---] [---]
 * [MPU REG 7] [                                   ] [---] [---]
 *
 * In User mode:
 *
 * [MPU REG 0] [ kernel TXT section                ] [R-X] [---] // syscall gate
 * [MPU REG 1] [ kernel DATA section               ] [RW-] [---] // syscall gate
 * [MPU REG 2] [ task TXT section                  ] [R-X] [R-X]
 * [MPU REG 3] [ task Data section                 ] [RW-] [RW-]
 * [MPU REG 4] [ task ressources bank 1, if needed ] [---] [---]
 * [MPU REG 5] [ task ressources bank 1, if needed ] [---] [---]
 * [MPU REG 6] [ task ressources bank 1, if needed ] [---] [---]
 * [MPU REG 7] [ task ressources bank 1, if needed ] [---] [---]
 *
 */
kstatus_t mgr_mm_init(void)
{
    kstatus_t status = K_STATUS_OKAY;
    mm_configured = SECURE_FALSE;
#ifdef CONFIG_HAS_MPU
    mpu_disable();
    status = mgr_mm_map_kernel_txt();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    status = mgr_mm_map_kernel_data();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    mpu_enable();
    mm_configured = SECURE_TRUE;
err:
#endif
    return status;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_mm_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif

kstatus_t mgr_mm_watchdog(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}

/**
 * @brief map a kernel device
 *
 * INFO: the kernel can map a single SoC device at a time. Be cautious.
 * This function do not check that a previous device is mapped, for performance
 * reasons. This is a kernel local specific behavior.
 *
 * This API is BSP specific, not using handles, as BSP do not know handles but yet
 * needs to map themselves. This API then use address/len informations of devices
 *
 * @param[in] address: device base address
 * @param[in] size: device size
 */
kstatus_t mgr_mm_map_kdev(uint32_t address, size_t len)
{
    kstatus_t status = K_STATUS_OKAY;
    if (mgr_mm_configured() == SECURE_TRUE) {
        struct mpu_region_desc kdev_config = {
            .id = MM_REGION_KERNEL_DEVICE,
            .addr = address,
            .size = mpu_convert_size_to_region(len),
            .access_perm = MPU_REGION_PERM_PRIV,
            .access_attrs = MPU_REGION_ATTRS_STRONGLY_ORDER,
            .mask = 0x0,
            .noexec = true,
        };
        status = mpu_load_configuration(&kdev_config, 1);
    }
    return status;
}

/**
 * @brief unmap a kernel device
 *
 * INFO: this function clear and disable the kernel device region. If nothing is
 * mapped, this has no impact (other than time cost).
 *
 * This API is BSP specific, not using handles, as BSP do not know handles but yet
 * needs to map themselves. This API then use address/len informations of devices
 */
kstatus_t mgr_mm_unmap_kdev(void)
{
    kstatus_t status = K_STATUS_OKAY;
    if (likely(mgr_mm_configured() == SECURE_TRUE)) {
        mpu_clear_region(MM_REGION_KERNEL_DEVICE);
    }
    return status;
}
