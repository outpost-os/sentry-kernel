// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file MPU manipulation primitives implementation with hardened support
 * (store, load and check)
 */

#if 0
/* this is CM7 MPU config, to be removed & replaced */
struct mpu_region_desc memory_regions_config[] = {
    /* ITCM MPU configuration, normal memory, nocache, executable */
    {
        .id = 0,
        .addr = ITCM_BASE_ADDR,
        .size = MPU_REGION_SIZE_128KB,
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
        .mask = 0x0,
        .noexec = false,
    },
    /* DTCM MPU configuration, normal memory, nocache, non executable */
    {
        .id = 1,
        .addr = DTCM_BASE_ADDR,
        .size = MPU_REGION_SIZE_128KB,
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
        .mask = 0x0,
        .noexec = true,
    },
    /* system memory, strongly ordered */
    {
        .id = 2,
        .addr = SYSMEM_BASE,
        .size = MPU_REGION_SIZE_1MB,
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_STRONGLY_ORDER,
        .mask = 0x0,
        .noexec = true,
    },
    /* AIPS1235 memory, this is non-shared device memory */
    {
        .id = 3,
        .addr = AIPS1235_BASE,
        .size = MPU_REGION_SIZE_16MB,
        .access_perm = MPU_REGION_PERM_PRIV,
        /*
         * XXX:
         * shared ?
         *  implies bufferable and thus memory barrier for writer buffer sync
         *  also need to enable buffer access per bidge at AIPSTZ level
         */
        .access_attrs = MPU_REGION_ATTRS_DEVICE,
        .mask = 0x0,
        .noexec = true,
    },
    /* AIPS4 memory, this is non-shared device memory */
    {
        .id = 4,
        .addr = AIPS4_BASE,
        .size = MPU_REGION_SIZE_4MB,
        .access_perm = MPU_REGION_PERM_PRIV,
        /*
         * XXX:
         * shared ?
         *  implies bufferable and thus memory barrier for writer buffer sync
         *  also need to enable buffer access per bidge at AIPSTZ level
         */
        .access_attrs = MPU_REGION_ATTRS_DEVICE,
        .mask = 0x0,
        .noexec = true,
    },
    /* OCRAM_S memory, normal memory nocache */
    {
        .id = 5,
        .addr = OCRAM_S_BASE,
        /* OCRAM S is actually 36 KiB, the 28 upper KiB are reserved */
        .size = ARM_MPU_REGION_SIZE_64KB,
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
        .mask = 0x0, /* XXX: do not enable all sub-regions */
        .noexec = true,
    },
    /* OCRAM memory, normal memory nocache */
    {
        .id = 6,
        .addr = OCRAM_BASE,
        /* OCRAM S is actually 576 KiB, the upper 448 KiB and the next 1 MiB are reserved */
        .size = ARM_MPU_REGION_SIZE_2MB,
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_NORMAL_NOCACHE,
        .mask = 0x0, /* XXX: do not enable all sub-regions */
        .noexec = true,
    },
#if CONFIG_ENABLE_DISPLAY == 1
    /* DDR memory, normal memory cache/bufferable, read allocate */
    {
        .id = 7,
        .addr = CONFIG_FB_NWD_BASE_PADDR,
        .size = ARM_MPU_REGION_SIZE_64MB,
        .access_perm = MPU_REGION_PERM_PRIV,
        .access_attrs = MPU_REGION_ATTRS_NORMAL_CACHE,
        .mask = 0x0,
        .noexec = true,
    },
#endif

};
#endif
