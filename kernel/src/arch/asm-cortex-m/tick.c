// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <sentry/arch/asm-cortex-m/tick.h>
#include <sentry/arch/asm-cortex-m/systick.h>
#include <sentry/arch/asm-cortex-m/dwt.h>
#include <bsp/drivers/clk/rcc.h>

static uint64_t cycle_jiffies;
static uint64_t dwt_snap;

void systime_init(void)
{
    cycle_jiffies = dwt_cyccnt();
    /*
     * dwt cyccnt is initialized at early boot
     * Thus, we can measure boot time precisely.
     */
    dwt_snap = cycle_jiffies;
    /* central systime init systick on ARM platform too */
    systick_init();
}

/**
 * read, update and return the current cycle count since startup. Can
 * be called multiple time, with a non-periodic behavior, but non-reentrant
 */
uint64_t systime_get_cycle(void)
{
    uint32_t dwt = dwt_cyccnt();
    if (dwt > dwt_snap) {
        /* dwt has incremented since last handler call. add increment only */
        cycle_jiffies += (dwt - dwt_snap);
    } else {
        /* dwt has reseted since last handler call, add current value + previous
         * residual
         */
        cycle_jiffies += dwt;
        cycle_jiffies += (0xffffffffUL - dwt_snap);
    }
    dwt_snap = dwt;
    return cycle_jiffies;
}
