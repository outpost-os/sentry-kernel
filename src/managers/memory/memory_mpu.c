// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry memory manager implementation
 */
#include <inttypes.h>

#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-generic/membarriers.h>


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

stack_frame_t *memfault_handler(stack_frame_t *frame)
{
    /* FIXME: differenciate userspace & kernel fault here */
    __do_panic();
    return frame;
}

/*
 * Per region function implementation, forced inline, but
 * clearer.
 */

__STATIC_INLINE kstatus_t mgr_mm_map_kernel_txt(void)
{
    kstatus_t status = K_STATUS_OKAY;
    struct mpu_region_desc kernel_txt_config = {
        .id = 0,
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
        .id = 1,
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

#if defined(__arm__)
__STATIC_INLINE kstatus_t mgr_mm_map_kernel_armm_scs(void)
{

    kstatus_t status = K_STATUS_OKAY;
    /* ARM system memory, strongly ordered */
    struct mpu_region_desc kernel_scs_config = {
        .id = 3,
        .addr = SCS_BASE,
        .size = MPU_REGION_SIZE_1MB,
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_STRONGLY_ORDER,
        .mask = 0x0,
        .noexec = true,
    };
    status = mpu_load_configuration(&kernel_scs_config, 1);
    return status;
};
#endif

/**
 * @brief map a region of type reg_type, identified by reg_handle, on taskh request
 *
 * If mapping a kernel anon region (txt, data):
 *  - reg_handle is ignored and MUST be 0
 *  - requester is ignored and MUST be 0
 * If mapping a kernel ressource (device):
 *  - reg_handle is a valid kernel devh_t
 *  - requester is ignored nd MUST be 0
 * If mapping a userspace anon region (txt, data):
 *  - reg_handle is ignored and MUST be 0
 *  - requester is the taskh_t requiring the mapping
 * If mapping a userspace ressource (device, shm):
 * - reg_handle is a ressource identifier (devh_t, shmh_t)
 * - requester is the taskh_t requiring the mapping
 */
kstatus_t mgr_mm_map(mm_region_t reg_type, uint32_t reg_handle, taskh_t requester)
{
    kstatus_t status = K_SECURITY_INTEGRITY;
    const task_meta_t *meta;
    switch (reg_type) {
#if defined(__arm__)
        case MM_REGION_KERNEL_SYSARM:
            if (unlikely(handle_convert_to_u32(requester) == 0x0)) {
                /* only kernel itself can map kernel content */
                goto err;
            }
            status = mgr_mm_map_kernel_armm_scs();
            break;
#endif
        case MM_REGION_TASK_SVC_EXCHANGE:
            /* FIXME: define if this is a real need, instead of through a mm_resize(TASK_DATA) instead */
            break;
        case MM_REGION_TASK_TXT:
            if (unlikely((status = mgr_task_get_metadata(requester, &meta)) == K_ERROR_INVPARAM)) {
                /* invalid task handle */
                pr_err("failed to get metadata for task %08x",
                    handle_convert_to_u32(requester));
                goto err;
            }
            pr_debug("mapping task %08x code section, from %p size %p",
               handle_convert_to_u32(requester), meta->s_text, meta->text_size);
            struct mpu_region_desc user_txt_config = {
                .id = 4,
                .addr = (uint32_t)meta->s_text,
                .size = mpu_convert_size_to_region(meta->text_size),
                .access_perm = MPU_REGION_PERM_RO,
                .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
                .mask = 0x0,
                .noexec = false,
            };

            status = mpu_load_configuration(&user_txt_config, 1);
            break;
        case MM_REGION_TASK_DATA:
            if (unlikely((status = mgr_task_get_metadata(requester, &meta)) == K_ERROR_INVPARAM)) {
                /* invalid task handle */
                pr_err("failed to get metadata for task %08x",
                    handle_convert_to_u32(requester));
                goto err;
            }
            pr_debug("mapping task %08x data section, from %p size %p",
               handle_convert_to_u32(requester), meta->s_data, meta->data_size);
            struct mpu_region_desc user_data_config = {
                .id = 5,
                .addr = (uint32_t)meta->s_data, /* To define: where start the task RAM ? .data ? other ? */
                .size = mpu_convert_size_to_region(meta->data_size),   /* FIXME data_size is a concat of all datas sections */
                .access_perm = MPU_REGION_PERM_FULL,
                .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
                .mask = 0x0,
                .noexec = true,
            };
            status = mpu_load_configuration(&user_data_config, 1);
            break;
        case MM_REGION_TASK_DEVICE:
            /** TODO: needs dev manager */
            break;
        case MM_REGION_TASK_SHM:
            /** TODO: define SHM handling (in this manager) */
            break;
        default:
            goto err;
    }
err:
    return status;
}

/**
 * @brief unmap a region of type reg_type, identified by reg_handle, on taskh request
 *
 */
kstatus_t mgr_mm_ummap(mm_region_t reg_type, uint32_t reg_handle, taskh_t requester)
{
    kstatus_t status = K_SECURITY_INTEGRITY;
    switch (reg_type) {
#if defined(__arm__)
        case MM_REGION_KERNEL_SYSARM:
            if (unlikely(handle_convert_to_u32(requester) == 0x0UL)) {
                /* only kernel itself can unmap kernel content */
                goto err;
            }
            mpu_clear_region(3);
            status = K_STATUS_OKAY;
            break;
#endif
        case MM_REGION_TASK_TXT:
            if (unlikely(handle_convert_to_u32(requester) == 0x0UL)) {
                /* only kernel itself can a task txt */
                goto err;
            }
            mpu_clear_region(4);
            status = K_STATUS_OKAY;
            break;
        case MM_REGION_TASK_SVC_EXCHANGE:
            if (unlikely(unlikely(handle_convert_to_u32(requester) == 0x0UL))) {
                /* only kernel itself can a task svc_exchange */
                goto err;
            }
            mpu_clear_region(5);
            status = K_STATUS_OKAY;
            break;
        case MM_REGION_TASK_DATA:
            if (unlikely(handle_convert_to_u32(requester) == 0x0UL)) {
                /* only kernel itself can a task data */
                goto err;
            }
            mpu_clear_region(5);
            status = K_STATUS_OKAY;
            break;
        case MM_REGION_TASK_DEVICE:
            /** TODO: needs dev manager. requester can be a user task */
            break;
        case MM_REGION_TASK_SHM:
            /** TODO: define SHM handling (in this manager). requester can be a user task */
            break;
        default:
            goto err;
    }
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
 * [MPU REG 3] [ ARM SCS region                    ] [RW-] [---] SO, only on __arm__
 * [MPU REG 4] [                                   ] [---] [---]
 * [MPU REG 5] [ task Data SVD-exchange region     ] [RW-] [RW-]
 *
 * In User mode:
 *
 * [MPU REG 0] [ kernel TXT section                ] [R-X] [---] // syscall gate
 * [MPU REG 1] [ kernel DATA section               ] [RW-] [---] // syscall gate
 * [MPU REG 2] [ task ressources bank 2, if needed ] |---] [---]
 * [MPU REG 3] [ task ressources bank 2, if needed ] [---] [---]
 * [MPU REG 4] [ task TXT section                  ] [R-X] [R-X]
 * [MPU REG 5] [ task Data section                 ] [RW-] [RW-]
 * [MPU REG 6] [ task ressources bank 1, if needed ] [---] [---]
 * [MPU REG 7] [ task ressources bank 1, if needed ] [---] [---]
 *
 *
 * info: reg 2 to be removed & replaced with dynamic, per device map/unmap mechanism
 * through -dt struct generation (each device -dt.c generated code implement devxxx_map() and
 * devxx_unmap() that call the current mgr_mm_map() and mgr_mm_unmap() with the dt-based
 * generated structure containing base addr & size)
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
#if defined(__arm__)
    status = mgr_mm_map_kernel_armm_scs();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
#endif
    mpu_enable();
    mm_configured = SECURE_TRUE;
err:
#endif
    return status;
}

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
            .id = 2,
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
        mpu_clear_region(2);
    }
    return status;
}
