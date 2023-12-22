// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ARCH_MEMORY_H
#define ARCH_MEMORY_H

#include <inttypes.h>
#include <stddef.h>
#include <string.h>
#include <sentry/ktypes.h>

/* the opaque is mapped on u64 on x86_64 */
typedef uint64_t layout_ressource_t;

#define TASK_MAX_RESSOURCES_NUM (6)

/**
 * MPU-implementation generic region definition. Can be used as well for ARM as for RISC-V
 */
struct mpu_region_desc {
    uint32_t addr;          /**< memory region start addr (must be align on 32 bytes boundary) */
    uint8_t  id;            /**< memory region ID */
    uint8_t  size;          /**< memory region size => 2^(size + 1) */
    uint8_t  access_perm;   /**< Read Write access permission for supervisor and/or user mode*/
    uint8_t  mask;          /**< sub region enable mask */
    uint32_t access_attrs;  /**< Cached/Buffered/Shared access attributes */
    bool     noexec;        /**< No-exec bit */
};

/* sample test only implementation for unit testing. */

/**
 * NOTE: a fully portable kernel should abstract the mpu vs mmu API at task manager level
 */

static inline uint8_t mpu_get_id_from_ressource(const layout_ressource_t ressource __attribute__((unused)))
{
    /* sample function: fixing region id to 3 here */
    return 3;
}

static inline kstatus_t mpu_forge_unmapped_ressource(uint8_t id __attribute__((unused)), layout_ressource_t* ressource)
{
    if (ressource == NULL) {
        return K_ERROR_INVPARAM;
    }
    return K_STATUS_OKAY;
}

static inline kstatus_t mpu_forge_ressource(const struct mpu_region_desc *desc,
                                                   layout_ressource_t *ressource)
{
    if ((desc == NULL) || (ressource == NULL)) {
        return K_ERROR_INVPARAM;
    }
    return K_STATUS_OKAY;
}

#endif/*!ARCH_MEMORY_H*/
