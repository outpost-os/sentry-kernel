/*
 * SPDX-FileCopyrightText: 2023 Ledger SAS
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * MPU implementation header for PMSAv7 ARM cortex-M MPU.
 */

#ifndef __ARCH_MPU_H
#error "this is an arch specific header, **do not** include directly, use <arch/mpu.h> instead"
#endif

#ifndef __ARCH_ARM_PMSA_V7_H
#define __ARCH_ARM_PMSA_V7_H

#include <inttypes.h>
#include <stddef.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/ktypes.h>

/** MPU Access Permission no access */
#define MPU_REGION_PERM_NONE ARM_MPU_AP_NONE
/** MPU Access Permission privileged access only */
#define MPU_REGION_PERM_PRIV ARM_MPU_AP_PRIV
/** MPU Access Permission privileged read-write, unprivileged access read-only */
#define MPU_REGION_PERM_UNPRIV_RO ARM_MPU_AP_URO
/** MPU Access Permission full access */
#define MPU_REGION_PERM_FULL ARM_MPU_AP_FULL
/** MPU Access Permission privileged access read-only */
#define MPU_REGION_PERM_PRIV_RO ARM_MPU_AP_PRO
/** MPU Access Permission privileged/unprivileged read-only access */
#define MPU_REGION_PERM_RO ARM_MPU_AP_RO
/** MPU Access attribute for strongly ordered memory */
#define MPU_REGION_ATTRS_STRONGLY_ORDER ARM_MPU_ACCESS_ORDERED

/** MPU Access attribute for device memory */
#define MPU_REGION_ATTRS_DEVICE ARM_MPU_ACCESS_DEVICE(0UL)

/** MPU Access attribute for non cached normal memory */
#define MPU_REGION_ATTRS_NORMAL_NOCACHE \
    ARM_MPU_ACCESS_NORMAL(ARM_MPU_CACHEP_NOCACHE, ARM_MPU_CACHEP_NOCACHE, 0UL)

/** MPU Access attribute for cached normal memory w/ write back and read allocate cache policy */
#define MPU_REGION_ATTRS_NORMAL_CACHE \
    ARM_MPU_ACCESS_NORMAL(ARM_MPU_CACHEP_WB_NWA, ARM_MPU_CACHEP_WB_NWA, 0UL)

/** MPU Access attribute for cached and shared normal memory w/ write back and read allocate cache policy */
#define MPU_REGION_ATTRS_NORMAL_CACHE_SHARED \
    ARM_MPU_ACCESS_NORMAL(ARM_MPU_CACHEP_WB_NWA, ARM_MPU_CACHEP_WB_NWA, 1UL)

/** MPU Region Size 32 Bytes */
#define MPU_REGION_SIZE_32B ARM_MPU_REGION_SIZE_32B
/** MPU Region Size 64 Bytes */
#define MPU_REGION_SIZE_64B ARM_MPU_REGION_SIZE_64B
/** MPU Region Size 128 Bytes */
#define MPU_REGION_SIZE_128B ARM_MPU_REGION_SIZE_128B
/** MPU Region Size 256 Bytes */
#define MPU_REGION_SIZE_256B ARM_MPU_REGION_SIZE_256B
/** MPU Region Size 512 Bytes */
#define MPU_REGION_SIZE_512B ARM_MPU_REGION_SIZE_512B
/** MPU Region Size 1 KByte */
#define MPU_REGION_SIZE_1KB ARM_MPU_REGION_SIZE_1KB
/** MPU Region Size 2 KBytes */
#define MPU_REGION_SIZE_2KB ARM_MPU_REGION_SIZE_2KB
/** MPU Region Size 4 KBytes */
#define MPU_REGION_SIZE_4KB ARM_MPU_REGION_SIZE_4KB
/** MPU Region Size 8 KBytes */
#define MPU_REGION_SIZE_8KB ARM_MPU_REGION_SIZE_8KB
/** MPU Region Size 16 KBytes */
#define MPU_REGION_SIZE_16KB ARM_MPU_REGION_SIZE_16KB
/** MPU Region Size 32 KBytes */
#define MPU_REGION_SIZE_32KB ARM_MPU_REGION_SIZE_32KB
/** MPU Region Size 64 KBytes */
#define MPU_REGION_SIZE_64KB ARM_MPU_REGION_SIZE_64KB
/** MPU Region Size 128 KBytes */
#define MPU_REGION_SIZE_128KB ARM_MPU_REGION_SIZE_128KB
/** MPU Region Size 256 KBytes */
#define MPU_REGION_SIZE_256KB ARM_MPU_REGION_SIZE_256KB
/** MPU Region Size 512 KBytes */
#define MPU_REGION_SIZE_512KB ARM_MPU_REGION_SIZE_512KB
/** MPU Region Size 1 MByte */
#define MPU_REGION_SIZE_1MB ARM_MPU_REGION_SIZE_1MB
/** MPU Region Size 2 MBytes */
#define MPU_REGION_SIZE_2MB ARM_MPU_REGION_SIZE_2MB
/** MPU Region Size 4 MBytes */
#define MPU_REGION_SIZE_4MB ARM_MPU_REGION_SIZE_4MB
/** MPU Region Size 8 MBytes */
#define MPU_REGION_SIZE_8MB ARM_MPU_REGION_SIZE_8MB
/** MPU Region Size 16 MBytes */
#define MPU_REGION_SIZE_16MB ARM_MPU_REGION_SIZE_16MB
/** MPU Region Size 32 MBytes */
#define MPU_REGION_SIZE_32MB ARM_MPU_REGION_SIZE_32MB
/** MPU Region Size 64 MBytes */
#define MPU_REGION_SIZE_64MB ARM_MPU_REGION_SIZE_64MB
/** MPU Region Size 128 MBytes */
#define MPU_REGION_SIZE_128MB ARM_MPU_REGION_SIZE_128MB
/** MPU Region Size 256 MBytes */
#define MPU_REGION_SIZE_256MB ARM_MPU_REGION_SIZE_256MB
/** MPU Region Size 512 MBytes */
#define MPU_REGION_SIZE_512MB ARM_MPU_REGION_SIZE_512MB
/** MPU Region Size 1 GByte */
#define MPU_REGION_SIZE_1GB ARM_MPU_REGION_SIZE_1GB
/** MPU Region Size 2 GBytes */
#define MPU_REGION_SIZE_2GB ARM_MPU_REGION_SIZE_2GB
/** MPU Region Size 4 GBytes */
#define MPU_REGION_SIZE_4GB ARM_MPU_REGION_SIZE_4GB

#define IS_POWEROFTWO(s) ((s != 0) && ((s & (s - 1)) == 0))

#define ROUNDUP_TO_POWEROFTWO(s) (1 << (32 - __builtin_clz (s - 1)))

static inline uint8_t mpu_convert_size_to_region(uint32_t size) {
    if (unlikely(size < 32)) {
        size = 32; /* rounding to minimum MPU size supported */
    }
    /* TODO overflow check here */
    if (unlikely(!IS_POWEROFTWO(size))) {
        size = ROUNDUP_TO_POWEROFTWO(size);
    }
    /* get back the number of preceding 0 before '1' (shift calculation) */
    uint8_t shift = __builtin_ffsl(size) - 1;
    /*
     * MPU region size is correlated to the shift value, starting with 32B=0x4.
     * 32 is encoded with 0b100000 (shift == 5). We only have to return shift - 1
     * to get the correct result
     */
    return shift -1;
}

/**
 * Enable PMSAv7 MPU
 */
#define mpu_enable(x) ARM_MPU_Enable(MPU_CTRL_PRIVDEFENA_Msk | MPU_CTRL_HFNMIENA_Msk)

/**
 * Disable PMSAv7 MPU
 */
#define mpu_disable ARM_MPU_Disable

/**
 * Clear (and disable) MPU region configuration
 */
#define mpu_clear_region(rnr) ARM_MPU_ClrRegion((rnr))

/**
 * Load memory regions description table in MPU
 */
__STATIC_FORCEINLINE kstatus_t mpu_load_configuration(const struct mpu_region_desc *region_descs,
                            size_t count)
{
    kstatus_t status = K_ERROR_INVPARAM;
    uint32_t rbar;
    uint32_t rasr;
    const struct mpu_region_desc *desc = NULL;

    if (region_descs == NULL) {
        goto end;
    }

    for (size_t i = 0UL; i < count; i++) {
        desc = region_descs + i;
#ifndef __FRAMAC__
        rbar = ARM_MPU_RBAR(desc->id, desc->addr);
        rasr = ARM_MPU_RASR_EX(desc->noexec ? 1UL : 0UL,
                               desc->access_perm,
                               desc->access_attrs,
                               desc->mask,
                               desc->size);
        ARM_MPU_SetRegion(rbar, rasr);
#endif
    }
    status = K_STATUS_OKAY;
end:
    return status;
}

#endif /* __ARCH_ARM_PMSA_V7_H */
