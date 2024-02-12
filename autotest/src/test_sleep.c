#include <inttypes.h>
#include <testlib/log.h>
#include <testlib/assert.h>
#include <uapi/uapi.h>
#include "test_sleep.h"

void test_sleep(void)
{
    TEST_SUITE_START("sys_sleep");
    test_sleep_return();
    test_sleep_duration();
    TEST_SUITE_END("sys_sleep");
}

void test_sleep_return(void)
{
    SleepDuration duration;
    uint32_t sleep_time = 1000UL;
    duration.tag = SLEEP_DURATION_ARBITRARY_MS;
    duration.arbitrary_ms = sleep_time;

    TEST_START();
    ASSERT_EQ(sys_sleep(duration, SLEEP_MODE_DEEP), STATUS_OK);
    TEST_END();

    return;
}

void test_sleep_duration(void)
{
    SleepDuration duration;
    uint32_t duration_vector[]= {
        1000UL,
        100UL,
        2000UL,
        50UL,
        20UL,
        10UL
    };

    duration.tag = SLEEP_DURATION_ARBITRARY_MS;
    for (uint8_t subtest = 0; subtest < 6; ++subtest) {
        uint32_t sleep_time = duration_vector[subtest];
        uint64_t calculated;
        uint64_t start, stop;
        Status   cycle_start_st, sleep_st, cycle_end_st;
        duration.arbitrary_ms = sleep_time;
        TEST_START();

        /* as svc exchange is zeroified by sys_log usage,
         * and because logging is impacting the duration, we first
         * get all the values, and then assert them
         */
        cycle_start_st = sys_get_cycle(PRECISION_MILLISECONDS);
        copy_to_user((uint8_t*)&start, sizeof(uint64_t));
        sleep_st = sys_sleep(duration, SLEEP_MODE_DEEP);
        cycle_end_st = sys_get_cycle(PRECISION_MILLISECONDS);
        copy_to_user((uint8_t*)&stop, sizeof(uint64_t));

        ASSERT_EQ(cycle_start_st, STATUS_OK);
        ASSERT_EQ(sleep_st, STATUS_OK);
        ASSERT_EQ(cycle_end_st, STATUS_OK);
        ASSERT_GE((uint32_t)(stop - start), duration_vector[subtest]);
        TEST_END();
    }

    return;
}
