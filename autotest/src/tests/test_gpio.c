#include <inttypes.h>
#include <testlib/log.h>
#include <testlib/assert.h>
#include <uapi/uapi.h>
#include <devices-dt.h>
#include "test_gpio.h"


void test_gpio_on(void)
{
    Status res;
    devh_t dev;
    TEST_START();
    res = sys_get_device_handle((uint8_t)devices[0].id);
    copy_to_user((uint8_t*)&dev, sizeof(devh_t));
    ASSERT_EQ(res, STATUS_OK);
    LOG("handle is %lx", dev);
    res = sys_gpio_configure(dev, 0);
    ASSERT_EQ(res, STATUS_OK);
    res = sys_gpio_set(dev, 0, 1);
    ASSERT_EQ(res, STATUS_OK);
    TEST_END();
}

void test_gpio_off(void)
{
    Status res;
    devh_t dev;

    TEST_START();
    res = sys_get_device_handle((uint8_t)devices[0].id);
    copy_to_user((uint8_t*)&dev, sizeof(devh_t));
    ASSERT_EQ(res, STATUS_OK);
    LOG("handle is %lx", dev);
    res = sys_gpio_configure(dev, 0);
    ASSERT_EQ(res, STATUS_OK);
    res = sys_gpio_set(dev, 0, 0);
    ASSERT_EQ(res, STATUS_OK);
    TEST_END();
}

void test_gpio_toggle(void)
{
    Status res;
    SleepDuration duration;
    devh_t dev;

    duration.tag = SLEEP_DURATION_ARBITRARY_MS;
    duration.arbitrary_ms = 250; /* 250 ms*/
    TEST_START();
    res = sys_get_device_handle((uint8_t)devices[0].id);
    copy_to_user((uint8_t*)&dev, sizeof(devh_t));
    res = sys_gpio_configure(dev, 0);
    ASSERT_EQ(res, STATUS_OK);
    for (uint8_t i = 0; i < 10; ++i) {
        res = sys_gpio_toggle(dev, 0);
        ASSERT_EQ(res, STATUS_OK);
        sys_sleep(duration, SLEEP_MODE_DEEP);
    }
    TEST_END();
}

void test_gpio_invalid_io(void)
{
    Status res;
    devh_t dev;

    TEST_START();
    res = sys_get_device_handle((uint8_t)devices[0].id);
    copy_to_user((uint8_t*)&dev, sizeof(devh_t));
    res = sys_gpio_configure(dev, 4);
    ASSERT_EQ(res, STATUS_INVALID);
    res = sys_gpio_configure(dev, 8);
    ASSERT_EQ(res, STATUS_INVALID);
    res = sys_gpio_configure(dev, 250);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}

void test_gpio_invalid_devh(void)
{
    Status res;
    devh_t dev = 1;

    TEST_START();
    res = sys_gpio_configure(dev, 1);
    ASSERT_EQ(res, STATUS_INVALID);
    TEST_END();
}


void test_gpio(void) {
#if DEVICE_LIST_SIZE > 0
    SleepDuration duration;
    duration.tag = SLEEP_DURATION_ARBITRARY_MS;
    duration.arbitrary_ms = 1000; /* 1000 ms to be visible */
    /* we need at least one led device generated from DTS */
    /** XXX: we should be able to handle multiple devices, and thus
     * have the hability to differenciate them
     */
    TEST_SUITE_START("sys_gpio");
    test_gpio_toggle();
    test_gpio_off();
    sys_sleep(duration, SLEEP_MODE_DEEP);
    test_gpio_on();
    sys_sleep(duration, SLEEP_MODE_DEEP);
    test_gpio_off();
    test_gpio_invalid_io();
    test_gpio_invalid_devh();
    TEST_SUITE_END("sys_gpio");
#endif
}
