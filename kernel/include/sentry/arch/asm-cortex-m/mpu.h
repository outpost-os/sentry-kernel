// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __ARCH_MPU_H
#define __ARCH_MPU_H

/**
 * \file MPU manipulation API for upper layer (memory unit)
 */
#include <stdint.h>
#include <stdbool.h>

struct mpu_region_desc {
    uint32_t addr;          /**< memory region start addr (must be align on 32 bytes boundary) */
    uint8_t  id;            /**< memory region ID */
    uint8_t  size;          /**< memory region size => 2^(size + 1) */
    uint8_t  access_perm;   /**< Read Write access permission for supervisor and/or user mode*/
    uint8_t  mask;          /**< sub region enable mask */
    uint32_t access_attrs;  /**< Cached/Buffered/Shared access attributes */
    bool     noexec;        /**< No-exec bit */
};

#if defined(CONFIG_ARCH_ARM_CORTEX_M) && \
    defined(CONFIG_HAS_MPU) && \
    defined(CONFIG_HAS_MPU_PMSA_V7)

#include <sentry/arch/asm-cortex-m/mpu_pmsa_v7.h>

#elif defined(CONFIG_ARCH_ARM_CORTEX_M) && \
      defined(CONFIG_HAS_MPU) && \
      defined(CONFIG_HAS_MPU_PMSA_V8)

/** FIXME: header to write, this will fail at compile time */
#include <sentry/arch/asm-cortex-m/mpu_pmsa_v8.h>
#else
# error "Unknown MPU type!"
#endif

/* a mpu ressource is a layout_ressource_t opaque. On thumbv7m (and thumbv8m) this is
  the concatenation of RBAR & RASR registers values.
  A task hold a table of this opaque, allowing store multiple upto 3 regions, to
  fast and efficiently keep trace of currently mapped regions.
*/
typedef ARM_MPU_Region_t layout_ressource_t;

#define TASK_MAX_RESSOURCES_NUM (CONFIG_NUM_MPU_REGIONS - 2)


__STATIC_FORCEINLINE uint8_t mpu_get_id_from_ressource(const layout_ressource_t ressource)
{
    uint8_t id = (uint8_t)((ressource.RBAR & MPU_RBAR_REGION_Msk) >> MPU_RBAR_REGION_Pos);
    return id;
}

__STATIC_FORCEINLINE kstatus_t mpu_forge_unmapped_ressource(uint8_t id, layout_ressource_t* ressource)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(ressource == NULL)) {
        goto end;
    }
    ressource->RBAR = ARM_MPU_RBAR(id, 0x0UL);
    ressource->RASR = 0x0UL;
    status = K_STATUS_OKAY;
end:
    return status;
}

__STATIC_FORCEINLINE kstatus_t mpu_forge_ressource(const struct mpu_region_desc *desc,
                                                   layout_ressource_t *ressource)
{
    kstatus_t status = K_ERROR_INVPARAM;
    uint32_t rbar;
    uint32_t rasr;

    if (unlikely((desc == NULL) || (ressource == NULL))) {
        goto end;
    }
    ressource->RBAR = ARM_MPU_RBAR(desc->id, desc->addr);
    ressource->RASR = ARM_MPU_RASR_EX(desc->noexec ? 1UL : 0UL,
                           desc->access_perm,
                           desc->access_attrs,
                           desc->mask,
                           desc->size);
    status = K_STATUS_OKAY;
end:
    return status;
}

__STATIC_FORCEINLINE void mpu_fastload(const layout_ressource_t *ressource, uint8_t num_ressources)
{
    __ISB();
    __DSB();
    ARM_MPU_Load(ressource, num_ressources);
    __ISB();
    __DSB();
}

__STATIC_FORCEINLINE kstatus_t mpu_get_free_id(const layout_ressource_t* ressource, uint8_t num_ressources, uint8_t *id)
{
    kstatus_t status = K_ERROR_NOENT;
    for (uint8_t i = 0; i < num_ressources; ++i) {
        if (ressource->RASR == 0x0UL) {
            *id = (uint8_t)((ressource->RBAR & MPU_RBAR_REGION_Msk) >> MPU_RBAR_REGION_Pos);
            status = K_STATUS_OKAY;
            break;
        }
    }
    return status;
}

__STATIC_FORCEINLINE kstatus_t mpu_get_id_from_address(const layout_ressource_t* ressource, uint8_t num_ressources, size_t addr, uint8_t *id)
{
    kstatus_t status = K_ERROR_NOENT;
    for (uint8_t i = 0; i < num_ressources; ++i) {
        if ((ressource->RBAR & MPU_RBAR_ADDR_Msk) == addr) {
            *id = (uint8_t)((ressource->RBAR & MPU_RBAR_REGION_Msk) >> MPU_RBAR_REGION_Pos);
            status = K_STATUS_OKAY;
            break;
        }
    }
    return status;
}

#endif/*__ARCH_MPU_H*/
