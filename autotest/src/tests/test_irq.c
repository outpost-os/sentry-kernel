// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <string.h>
#include <testlib/log.h>
#include <testlib/assert.h>
#include <uapi/uapi.h>
#include <uapi/dma.h>
#include <shms-dt.h>
#include "test_dma.h"

static void test_irq_init(void)
{
    return;
}

static void test_irq_spawn_one_it(void)
{
    return;
}

void test_irq(void)
{
    Status res;

    TEST_SUITE_START("sys_irq");
    /* init timer for IRQ, no IT enabled yet */
    test_irq_init();
    test_irq_spawn_one_it();
    TEST_SUITE_END("sys_irq");
    return;
}
