#include <inttypes.h>
#include <testlib/log.h>
#include <testlib/assert.h>
#include <uapi/uapi.h>
#include <uapi/capability.h>
#include <devices-dt.h>
#include "test_gpio.h"

/* FIXME: we need an uapi way to gen devh from dev id */
typedef struct kdevh {
    uint32_t dev_cap : 12; /**< device capability (unique capa per device) */
    uint32_t reserved : 1; /**< reserved field */
    uint32_t id : 16;      /**< device unique identifier on the system */
    uint32_t family : 3;   /**< handle familly */
} kdevh_t;


static inline devh_t forge_devh(uint32_t id)
{
    /*@ assert \valid_read(device); */
    union udh {
        const devh_t *dh;
        const kdevh_t *kdh;
    };
    kdevh_t kdevh = {
        .dev_cap = 0, //sentry_capability_t_DEV_IO.bits,
        .reserved = 0,
        .id = (uint32_t)id,
        .family = 1UL,
    };
    union udh udh;
    udh.kdh = &kdevh;
    LOG("handle is %lx", *udh.dh);
    return *udh.dh;
}


void test_gpio_on(void)
{
    Status res;
    TEST_START();
    devh_t dev = forge_devh(devices[0].id);
    res = sys_gpio_configure(dev, 0);
    ASSERT_EQ(res, STATUS_OK);
    res = sys_gpio_set(dev, 0, 1);
    ASSERT_EQ(res, STATUS_OK);
    TEST_END();
}

void test_gpio_off(void)
{
    Status res;
    TEST_START();
    devh_t dev = forge_devh(devices[0].id);
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
    duration.tag = SLEEP_DURATION_ARBITRARY_MS;
    duration.arbitrary_ms = 250; /* 250 ms*/
    TEST_START();
    devh_t dev = forge_devh(devices[0].id);
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
    TEST_START();
    devh_t dev = forge_devh(devices[0].id);
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
    TEST_START();
    devh_t dev = 1;
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
