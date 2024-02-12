#include <inttypes.h>
#include <testlib/log.h>
#include <testlib/assert.h>
#include <uapi/uapi.h>
#include "test_cycles.h"

void test_cycles_precision(void)
{
    SleepDuration duration;
    uint32_t precision_vector[]= {
        PRECISION_MILLISECONDS,
        PRECISION_MICROSECONDS,
        PRECISION_NANOSECONDS,
        PRECISION_CYCLE
    };
    for (uint8_t subtest = 0; subtest < 4; ++subtest) {
        Status cycle_st;
        uint64_t milli, micro, nano, cycle;
        TEST_START();

        /* as svc exchange is zeroified by sys_log usage,
         * and because logging is impacting the duration, we first
         * get all the values, and then assert them
         */
        cycle_st = sys_get_cycle(PRECISION_MILLISECONDS);
        copy_to_user((uint8_t*)&milli, sizeof(uint64_t));

        ASSERT_EQ(cycle_st, STATUS_OK);
        ASSERT_GT(milli, 0ULL);

        cycle_st = sys_get_cycle(PRECISION_MICROSECONDS);
        copy_to_user((uint8_t*)&micro, sizeof(uint64_t));

        ASSERT_EQ(cycle_st, STATUS_OK);
        ASSERT_GT(micro, (milli*1000ULL));

        cycle_st = sys_get_cycle(PRECISION_NANOSECONDS);
        copy_to_user((uint8_t*)&nano, sizeof(uint64_t));

        ASSERT_EQ(cycle_st, STATUS_OK);
        ASSERT_GT(nano, (micro*1000ULL));

        cycle_st = sys_get_cycle(PRECISION_CYCLE);
        ASSERT_EQ(cycle_st, STATUS_DENIED);

        TEST_END();
    }

    return;
}


void test_cycles(void)
{
    TEST_SUITE_START("sys_cycles");
    test_cycles_precision();
    TEST_SUITE_END("sys_cycles");
}
