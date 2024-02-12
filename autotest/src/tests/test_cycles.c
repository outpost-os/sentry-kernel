#include <inttypes.h>
#include <testlib/log.h>
#include <testlib/assert.h>
#include <uapi/uapi.h>
#include "test_cycles.h"

void test_cycles_duration(void)
{
    SleepDuration duration;
    uint64_t micro, start, stop;
    uint32_t idx;
    TEST_START();
    /* as svc exchange is zeroified by sys_log usage,
     * and because logging is impacting the duration, we first
     * get all the values, and then assert them
     */
    /* rearm quantum first */
    sys_yield();
    sys_get_cycle(PRECISION_MICROSECONDS);
    copy_to_user((uint8_t*)&start, sizeof(uint64_t));
    for (idx = 0; idx <= 1000; ++idx) {
        sys_get_cycle(PRECISION_MICROSECONDS);
    }
    sys_get_cycle(PRECISION_MICROSECONDS);
    copy_to_user((uint8_t*)&stop, sizeof(uint64_t));

    LOG("average get_cycle cost: %lu", (uint32_t)((stop - start) / idx));

    /* rearm quantum first */
    sys_yield();
    sys_get_cycle(PRECISION_MICROSECONDS);
    copy_to_user((uint8_t*)&start, sizeof(uint64_t));
    for (idx = 0; idx <= 1000; ++idx) {
        sys_get_cycle(PRECISION_MICROSECONDS);
        copy_to_user((uint8_t*)&micro, sizeof(uint64_t));
    }
    sys_get_cycle(PRECISION_MICROSECONDS);
    copy_to_user((uint8_t*)&stop, sizeof(uint64_t));

    LOG("average get_cycle+copy cost: %lu", (uint32_t)((stop - start) / idx));


    TEST_END();
}

void test_cycles_precision(void)
{
    SleepDuration duration;
    Status cycle_st, milli_st, micro_st, nano_st;
    uint64_t milli, micro, nano, cycle;
    TEST_START();
    /* as svc exchange is zeroified by sys_log usage,
     * and because logging is impacting the duration, we first
     * get all the values, and then assert them
     */
    milli_st = sys_get_cycle(PRECISION_MILLISECONDS);
    copy_to_user((uint8_t*)&milli, sizeof(uint64_t));


    micro_st = sys_get_cycle(PRECISION_MICROSECONDS);
    copy_to_user((uint8_t*)&micro, sizeof(uint64_t));


    nano_st = sys_get_cycle(PRECISION_NANOSECONDS);
    copy_to_user((uint8_t*)&nano, sizeof(uint64_t));

    cycle_st = sys_get_cycle(PRECISION_CYCLE);


    ASSERT_EQ(milli_st, STATUS_OK);
    ASSERT_GT((int)milli, 0);

    ASSERT_EQ(micro_st, STATUS_OK);
    ASSERT_GT((int)((micro*1000ULL) - milli), 0);

    ASSERT_EQ(nano_st, STATUS_OK);
    ASSERT_GT((int)((nano*1000ULL) - micro), 0);

    ASSERT_EQ(cycle_st, STATUS_DENIED);

    TEST_END();

    return;
}


void test_cycles(void)
{
    TEST_SUITE_START("sys_cycles");
    test_cycles_duration();
    test_cycles_precision();
    TEST_SUITE_END("sys_cycles");
}
