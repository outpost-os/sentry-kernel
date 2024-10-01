// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <testlib/log.h>
#include <testlib/assert.h>
#include <uapi/uapi.h>
#include "test_dma.h"

#if CONFIG_HAS_GPDMA
static void test_dma_get_handle(dmah_t* streamh)
{
    Status res;
    TEST_START();
    res = sys_get_dma_stream_handle(0x1);
    copy_to_user((uint8_t*)streamh, sizeof(dmah_t));
    ASSERT_EQ(res, STATUS_OK);
    LOG("handle is %lx", *streamh);
    TEST_END();
}

static void test_dma_get_handle_inval(void)
{
    Status res;
    dmah_t stream = 0;
    TEST_START();
    res = sys_get_dma_stream_handle(0x42);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

static void test_dma_start_stream(dmah_t stream)
{
    Status res;
    TEST_START();
    /* not assigned */
    res = sys_dma_start_stream(stream);
    ASSERT_EQ(res, STATUS_INVALID);
    res = sys_dma_assign_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    /* assigned, should start */
    res = sys_dma_start_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    res = sys_dma_assign_stream(stream);
    ASSERT_EQ(res, STATUS_INVALID);
    res = sys_dma_start_stream(stream);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

static void test_dma_manipulate_stream_badhandle(void)
{
    Status res;
    TEST_START();
    res = sys_dma_start_stream(0);
    ASSERT_EQ(res, STATUS_INVALID);
    res = sys_dma_stop_stream(0);
    ASSERT_EQ(res, STATUS_INVALID);
    res = sys_dma_get_stream_status(0);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

static void test_dma_get_stream_status(dmah_t stream)
{
    Status res;
    TEST_START();
    res = sys_dma_get_stream_status(stream);
    ASSERT_EQ(res, STATUS_OK);
    TEST_END();
}

static void test_dma_stop_stream(dmah_t stream)
{
    Status res;
    TEST_START();
    res = sys_dma_stop_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    res = sys_dma_stop_stream(stream);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

static void test_dma_assign_unassign_stream(dmah_t stream)
{
    Status res;
    TEST_START();
    res = sys_dma_assign_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    res = sys_dma_assign_stream(stream);
    ASSERT_EQ(res, STATUS_INVALID);
    res = sys_dma_unassign_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    res = sys_dma_unassign_stream(stream);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

static void test_dma_start_n_wait_stream(dmah_t stream)
{
    Status res;
    TEST_START();
    res = sys_dma_assign_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    res = sys_dma_start_stream(stream);
    ASSERT_EQ(res, STATUS_OK);
    /* wait 50ms for DMA event, should rise in the meantime */
    res = sys_wait_for_event(EVENT_TYPE_DMA, 50);
    ASSERT_EQ(res, STATUS_OK);
    TEST_END();
}

#endif

void test_dma(void)
{
    dmah_t stream = 0;
    TEST_SUITE_START("sys_dma");
#if CONFIG_HAS_GPDMA
    test_dma_get_handle(&stream);
    test_dma_get_handle_inval();
    test_dma_manipulate_stream_badhandle();
    test_dma_assign_unassign_stream(stream);
    test_dma_start_n_wait_stream(stream);
    test_dma_start_stream(stream);
    test_dma_get_stream_status(stream);
    test_dma_stop_stream(stream);
#endif
    TEST_SUITE_END("sys_dma");
}
