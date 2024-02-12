#include <inttypes.h>
#include <testlib/log.h>
#include <testlib/assert.h>
#include <uapi/uapi.h>
#include "test_yield.h"

void test_yield(void)
{
    TEST_SUITE_START("sys_yield");
    Status ret;
    TEST_START();
    LOG("yielding...");
    ret = sys_yield();
    ASSERT_EQ(ret, STATUS_OK);
    LOG("yielding...");
    ret = sys_yield();
    ASSERT_EQ(ret, STATUS_OK);
    LOG("yielding...");
    ret = sys_yield();
    ASSERT_EQ(ret, STATUS_OK);
    TEST_END();
    TEST_SUITE_END("sys_yield");
}
