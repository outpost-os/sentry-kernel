#include <inttypes.h>
#include <testlib/log.h>
#include <testlib/assert.h>
#include <uapi/uapi.h>
#include "test_ipc.h"

void test_ipc_send_toobig(void)
{
    Status ret;
    taskh_t handle = 0;
    uint8_t len = CONFIG_SVC_EXCHANGE_AREA_LEN+1;
    ret = sys_get_process_handle(0xbabeUL);
    copy_to_user((uint8_t*)&handle, sizeof(taskh_t));
    ASSERT_EQ(ret, STATUS_OK);
    TEST_START();
    LOG("sending invalid IPC size %lu", (uint32_t)len);
    ret = sys_send_ipc(handle, len);
    ASSERT_EQ(ret, STATUS_INVALID);
    len = 255;
    LOG("sending invalid IPC size %lu", (uint32_t)len);
    ret = sys_send_ipc(handle, len);
    ASSERT_EQ(ret, STATUS_INVALID);
    TEST_END();
}

void test_ipc_send_invalidtarget(void)
{
    Status ret;
    TEST_START();
    LOG("sending IPC to invalid target");
    ret = sys_send_ipc(0xdead1001UL, 20);
    ASSERT_EQ(ret, STATUS_INVALID);
    TEST_END();
}

void test_ipc_sendrecv(void)
{
    static const char *msg = "hello it's autotest";
    Status ret;
    taskh_t handle = 0;
    ret = sys_get_process_handle(0xbabeUL);
    copy_to_user((uint8_t*)&handle, sizeof(taskh_t));
    LOG("handle is %lx", handle);
    ASSERT_EQ(ret, STATUS_OK);
    TEST_START();
    LOG("sending IPC to myself");
    copy_from_user(msg, 20);
    ret = sys_send_ipc(handle, 20);
    ASSERT_EQ(ret, STATUS_OK);
    TEST_END();
}

void test_ipc(void)
{
    TEST_SUITE_START("sys_ipc");

    test_ipc_sendrecv();
    test_ipc_send_invalidtarget();
    test_ipc_send_toobig();

    TEST_SUITE_END("sys_ipc");
}
