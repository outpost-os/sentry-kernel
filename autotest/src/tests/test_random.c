#include <inttypes.h>
#include <testlib/log.h>
#include <testlib/assert.h>
#include <uapi/uapi.h>
#include "test_random.h"



void test_random_sequence(void)
{
    Status ret;
    uint32_t rng;
    TEST_START();
    LOG("get back random value from KRNG");
    for (uint32_t idx = 0; idx < 5; ++idx) {
        ret = sys_get_random();
        copy_to_user((uint8_t*)&rng, sizeof(uint32_t));
        ASSERT_EQ(ret, STATUS_OK);
        LOG("rng retreived: 0x%lx", rng);
    }
    TEST_END();
}

void test_random_duration(void)
{
    uint64_t start, stop;
    uint32_t rng, idx;
    sys_yield();
    sys_get_cycle(PRECISION_MICROSECONDS);
    copy_to_user((uint8_t*)&start, sizeof(uint64_t));
    for (idx = 0; idx <= 1000; ++idx) {
        sys_get_random();
        copy_to_user((uint8_t*)&rng, sizeof(uint32_t));
    }
    sys_get_cycle(PRECISION_MICROSECONDS);
    copy_to_user((uint8_t*)&stop, sizeof(uint64_t));
    LOG("average get_random+copy cost: %lu", (uint32_t)((stop - start) / idx));
}

void test_random(void)
{
    TEST_SUITE_START("sys_get_random");

    test_random_sequence();
    test_random_duration();

    TEST_SUITE_END("sys_get_random");
}
