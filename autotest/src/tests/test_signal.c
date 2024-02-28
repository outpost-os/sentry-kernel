#include <inttypes.h>
#include <testlib/log.h>
#include <testlib/assert.h>
#include <uapi/uapi.h>
#include "test_ipc.h"


void test_signal_sendrecv(void)
{
    Status ret;
    taskh_t handle = 0;
    uint32_t timeout = 20UL;
    uint8_t data[CONFIG_SVC_EXCHANGE_AREA_LEN] = {0};
    ret = sys_get_process_handle(0xbabeUL);
    copy_to_user((uint8_t*)&handle, sizeof(taskh_t));
    LOG("handle is %lx", handle);
    ASSERT_EQ(ret, STATUS_OK);
    TEST_START();
    Signal sig = SIGNAL_ABORT;
    for (sig = SIGNAL_ABORT; sig <= SIGNAL_USR2; ++sig) {
        LOG("sending signal %u to myself", sig);
        ret = sys_send_signal(handle, sig);
    #if 1
        ret = sys_wait_for_event(EVENT_TYPE_SIGNAL, timeout);
        copy_to_user(data, 12);
        taskh_t *source = (taskh_t*)&data[4];
        uint32_t *signal = (uint32_t*)&data[8];
        LOG("%x:%u:%x%x: source=%lx, signal=%lu", data[0], data[1], data[2], data[3], *source, *signal);
        ASSERT_EQ(ret, STATUS_OK);
    #endif
    }
    TEST_END();
}

void test_signal(void)
{
    TEST_SUITE_START("sys_signal");

    test_signal_sendrecv();

    TEST_SUITE_END("sys_signal");
}
