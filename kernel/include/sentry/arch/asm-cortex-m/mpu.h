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

#endif/*__ARCH_MPU_H*/
