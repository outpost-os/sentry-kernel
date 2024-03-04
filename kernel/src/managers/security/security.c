// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <sentry/ktypes.h>
#include <sentry/managers/security.h>
#include <sentry/managers/task.h>
#include <sentry/managers/debug.h>
#include <sentry/arch/asm-generic/platform.h>
#include "entropy.h"

/** @def mask for dev capability. dev capa hold 11 first bytes of register */
#define CAPA_DEV_MASK ((0x1UL  << 12) - 1)
/** @def mask for sys capability, hold bits 12-15 */
#define CAPA_SYS_MASK (((0x1UL  << 16) - 1) & ~CAPA_DEV_MASK)
/*@ def mask for mem capability */
#define CAPA_MEM_MASK (((0x1UL << 20) - 1) & ~(CAP_DEV_MASK | CAPA_SYS_MASK))

kstatus_t mgr_security_init(void)
{
    kstatus_t status;
    pr_info("initialize security manager...");
    status = mgr_security_entropy_init();
#ifndef CONFIG_BUILD_TARGET_DEBUG
    pr_info("Forbid unaligned access");
    __platform_enforce_alignment();
#endif
    return status;
}

kstatus_t mgr_security_get_capa(taskh_t tsk, uint32_t *capas)
{
    kstatus_t status = K_ERROR_INVPARAM;
    const task_meta_t *meta;

    if (unlikely(capas == NULL)) {
        goto end;
    }
    if (unlikely(mgr_task_get_metadata(tsk, &meta) != K_STATUS_OKAY)) {
        /* current must be a valid task */
        goto end;
    }
    *capas = meta->capabilities;
end:
    return status;
}

secure_bool_t mgr_security_has_dev_capa(taskh_t tsk)
{
    secure_bool_t res = SECURE_FALSE;
    const task_meta_t *meta;

    if (unlikely(mgr_task_get_metadata(tsk, &meta) != K_STATUS_OKAY)) {
        /* current must be a valid task */
        goto end;
    }
    if ((meta->capabilities & CAPA_DEV_MASK) != 0) {
        res = SECURE_TRUE;
    }
end:
    return res;
}

secure_bool_t mgr_security_has_sys_capa(taskh_t tsk)
{
    secure_bool_t res = SECURE_FALSE;
    const task_meta_t *meta;

    if (unlikely(mgr_task_get_metadata(tsk, &meta) != K_STATUS_OKAY)) {
        /* current must be a valid task */
        goto end;
    }
    if ((meta->capabilities & CAPA_SYS_MASK) != 0) {
        res = SECURE_TRUE;
    }
end:
    return res;
}


secure_bool_t mgr_security_has_capa(taskh_t tsk, capability_t  capa)
{
    secure_bool_t res = SECURE_FALSE;
    const task_meta_t *meta;

    if (unlikely(mgr_task_get_metadata(tsk, &meta) != K_STATUS_OKAY)) {
        /* current must be a valid task */
        goto end;
    }
    if (meta->capabilities & capa) {
        res = SECURE_TRUE;
    }
end:
    return res;
}

secure_bool_t mgr_security_has_oneof_capas(taskh_t tsk, uint32_t capas)
{
    secure_bool_t res = SECURE_FALSE;
    const task_meta_t *meta;

    if (unlikely(mgr_task_get_metadata(tsk, &meta) != K_STATUS_OKAY)) {
        /* current must be a valid task */
        goto end;
    }
    if (meta->capabilities & capas) {
        res = SECURE_TRUE;
    }
end:
    return res;
}



#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_security_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    uint32_t seed;
    uint64_t start;
    uint64_t stop;
    uint64_t min = 0;
    uint64_t max = 0;
    uint64_t average = 0;
    uint32_t failures = 0;
    pr_autotest("START execute 256 entropy generation from entropy source");
    /* executing 256 random seed requests */
    for (uint32_t i=0; i < 256; ++i) {
        start = systime_get_cycle();
        if (unlikely(mgr_security_entropy_generate(&seed) != K_STATUS_OKAY)) {
            failures++;
        }
        stop = systime_get_cycle();
        uint64_t duration = stop - start;
        if (duration > max) {
            max = duration;
        }
        if ((min == 0) || (duration < min)) {
            min = duration;
        }
        average += duration;
    }
    /* average div 256 */
    average >>= 8;
    pr_autotest("entropy_generate min time: %llu", min);
    pr_autotest("entropy_generate max time: %llu", max);
    pr_autotest("entropy_generate average time: %llu", average);
    pr_autotest("entropy_generate failures: %llu", failures);
    pr_autotest("END");

    return status;
}
#endif
