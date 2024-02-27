#include <inttypes.h>
#include <testlib/log.h>
#include <testlib/assert.h>
#include <uapi/uapi.h>
#include "test_ipc.h"



void test_ipc_sendrecv(void)
{
    static const char *msg = "hello it's autotest";
    Status ret;
    taskh_t handle = 0;
    ret = sys_get_process_handle(0xbabeUL);
    copy_to_user((uint8_t*)&handle, sizeof(taskh_t));
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

    TEST_SUITE_END("sys_ipc");
}
