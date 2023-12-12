// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <sentry/ktypes.h>
#include <sentry/managers/security.h>
#include <sentry/managers/debug.h>
#include <sentry/arch/asm-generic/platform.h>
#include "entropy.h"

kstatus_t mgr_security_init(void)
{
    kstatus_t status;
    pr_info("initialize security manager...");
    status = mgr_security_entropy_init();
#ifndef CONFIG_BUILD_TARGET_DEBUG
    pr_info("disable unaligned access");
    __platform_enforce_alignment();
#endif
    return status;
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
