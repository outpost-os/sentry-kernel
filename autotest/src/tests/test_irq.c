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
#include <drivers/timer.h>

static void test_irq_spawn_two_it(void)
{
    Status res;
    uint8_t tab[128];
    uint32_t *IRQn;
    timer_enable_interrupt();
    timer_enable();
    /* waiting 1200ms */
    res = sys_wait_for_event(EVENT_TYPE_IRQ, 0);
    copy_to_user(&tab[0], sizeof(exchange_event_t) + 4);
    ASSERT_EQ(res, STATUS_OK);
    IRQn = (uint32_t*)&((exchange_event_t*)tab)->data;
    ASSERT_EQ(*IRQn, 49);
    timer_enable_interrupt();
    timer_enable();
    /* waiting 1200ms */
    res = sys_wait_for_event(EVENT_TYPE_IRQ, 0);
    copy_to_user(&tab[0], sizeof(exchange_event_t) + 4);
    ASSERT_EQ(res, STATUS_OK);
    IRQn = (uint32_t*)&((exchange_event_t*)tab)->data;
    ASSERT_EQ(*IRQn, 49);
    return;
}

static void test_irq_spawn_one_it(void)
{
    Status res;
    uint8_t tab[128];
    timer_enable_interrupt();
    timer_enable();
    /* waiting 1200ms */
    res = sys_wait_for_event(EVENT_TYPE_IRQ, 0);
    copy_to_user(&tab[0], sizeof(exchange_event_t) + 4);
    ASSERT_EQ(res, STATUS_OK);
    uint32_t *IRQn = (uint32_t*)&((exchange_event_t*)tab)->data;
    ASSERT_EQ(*IRQn, 49);
    return;
}


static void test_irq_spawn_periodic(void)
{
    Status res;
    uint8_t tab[128];
    uint8_t count;
    timer_enable_interrupt();
    timer_set_periodic();
    timer_enable();

    for (count = 0; count < 5; ++count) {
        LOG("interrupt count %d wait", count);
        res = sys_wait_for_event(EVENT_TYPE_IRQ, 0);
        copy_to_user(&tab[0], sizeof(exchange_event_t) + 4);
        ASSERT_EQ(res, STATUS_OK);
        uint32_t *IRQn = (uint32_t*)&((exchange_event_t*)tab)->data;
        ASSERT_EQ(*IRQn, 49);
        /* reeanble interrupt line (nvic unmasked)*/
        timer_enable_interrupt();
    }
}

void test_irq(void)
{
    Status res;

    TEST_SUITE_START("sys_irq");
    /* init timer for IRQ, no IT enabled yet */
    timer_map();
    timer_init();
    test_irq_spawn_one_it();
    test_irq_spawn_two_it();
    test_irq_spawn_periodic();
    timer_unmap();
    TEST_SUITE_END("sys_irq");
    return;
}
