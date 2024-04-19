// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry I/O manager
 */
#include <stdbool.h>

#include <uapi/handle.h>

#include <sentry/ktypes.h>

/* BSP headers */
#include <bsp/drivers/gpio/gpio.h>
#include <bsp/drivers/gpio/pinctrl.h>
#ifdef CONFIG_SOC_FAMILY_STM32
#include <bsp/drivers/exti/exti.h>
#endif

#include <sentry/managers/io.h>
#include <sentry/managers/device.h>

#define IOPIN_FROM_HANDLE



/**
 * @brief probe all BSP-related part of the I/O manipulation
 *
 * Kconfig already has auto-selected the various drviers needed for I/O. All
 * I/O drivers probing and manipulation is done through this manager's API.
 */
kstatus_t mgr_io_init(void)
{
    kstatus_t status = K_STATUS_OKAY;

    /* This backend should be generic to any SoC, any arch */
    /* FIXME: the probing of GPIO depends on the GPIO usage by devices.
       This information is the consequence of dtsi parsing */
#ifdef CONFIG_SOC_FAMILY_STM32
    /* STM32 BSP implement EXTI controler for external interrupt & events */
    if (unlikely((status = exti_probe()) != K_STATUS_OKAY)) {
        goto err;
    };
#endif
    /*
     *let's walk over devices to get back I/O port used, in order to probe() them
     *  at boot. We consider that there are at most 16 GPIO ports
     */
    uint8_t port_to_enable[16] = {0};
    uint8_t iterator = 0;
    const devinfo_t *devinfo;
    do {
        status = mgr_device_walk(&devinfo, iterator);
        if (status != K_STATUS_OKAY) {
            break;
        }
        if (devinfo->num_ios > 0) {
            /* device has I/O: associated GPIO port to probe */
            for (uint8_t io = 0; io < devinfo->num_ios; ++io) {
                /*@ assert(devinfo->ios[io].port < 16); */
                /* we only flag the port for probing, to avoid multiple probe() of the same port */
                port_to_enable[devinfo->ios[io].port] = 1;
            }
        }
        ++iterator;
    } while (status == K_STATUS_OKAY);
    /* all ports that do have a configured pinmux in device list are flagged to 1 */
    for (uint8_t i = 0; i < 16; ++i) {
        if (port_to_enable[i] == 1) {
            gpio_probe(i);
        }
    }
    status = K_STATUS_OKAY;
err:
    return status;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_io_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif

/**
 * @brief Set I/O identified by ioh
 *
 * This set output moode I/O line value to high level
 */
kstatus_t mgr_io_set(uint8_t ioport, uint8_t iopin)
{
    kstatus_t status = K_STATUS_OKAY;
    status = gpio_set(ioport, iopin);
    return status;
}

/**
 * @brief Reset I/O identified by ioh
 *
 * This set output moode I/O line value to low level
 */
kstatus_t mgr_io_reset(uint8_t ioport, uint8_t iopin)
{
    kstatus_t status = K_STATUS_OKAY;
    status = gpio_reset(ioport, iopin);
    return status;
}

/**
 * @brief Read I/O identified by ioh
 *
 * This get back current I/O line value, in both INPUT and OUTPUT mode
 */
/*@
  @ requires \valid(val);
  */
kstatus_t mgr_io_read(uint8_t ioport, uint8_t iopin, bool *val)
{
    kstatus_t status = K_STATUS_OKAY;
    status = gpio_get(ioport, iopin, val);
    return status;
}

/**
 * @brief Configure I/O identified by io_info_t
 *
 * io_info_t is a part of a devinfo structure (see uapi/device API)
 */
kstatus_t mgr_io_configure(io_info_t io)
{
    kstatus_t status = K_STATUS_OKAY;
    gpio_pinctrl_desc_t pinctrl_desc = {
        .mode = io.mode,
        .altfunc = io.af,
        .type = io.pupdr,
        .speed = io.speed,
        .pull_mode = io.ppull,
        .port_id = io.port,
        .pin = io.pin
    };
    status = gpio_pinctrl_configure(pinctrl_desc);
    return status;
}

/* About interrupt associated to I/O */


kstatus_t mgr_io_mask_interrupt(uint8_t ioport, uint8_t iopin)
{
    kstatus_t status = K_STATUS_OKAY;
#ifdef CONFIG_SOC_SUBFAMILY_STM32F4
    /* On stm32f4, IT0 == Px0, IT1 == Px1, and so on...
     * meaning that io pin (upto 15) define the associated EXTI line
     */
    status = exti_mask_interrupt(iopin);
#endif
    return status;
}

kstatus_t mgr_io_unmask_interrupt(uint8_t ioport, uint8_t iopin)
{
    kstatus_t status = K_STATUS_OKAY;
#ifdef CONFIG_SOC_SUBFAMILY_STM32F4
    /* On stm32f4, IT0 == Px0, IT1 == Px1, and so on...
     * meaning that io pin (upto 15) define the associated EXTI line
     */
    status = exti_unmask_interrupt(iopin);
#endif
    return status;
}

kstatus_t mgr_io_mask_event(uint8_t ioport, uint8_t iopin)
{
    kstatus_t status = K_STATUS_OKAY;
#ifdef CONFIG_SOC_SUBFAMILY_STM32F4
    /* On stm32f4, IT0 == Px0, IT1 == Px1, and so on...
     * meaning that io pin (upto 15) define the associated EXTI line
     */
    status = exti_mask_event(iopin);
#endif
    return status;
}

kstatus_t mgr_io_unmask_event(uint8_t ioport, uint8_t iopin)
{
    kstatus_t status = K_STATUS_OKAY;
#ifdef CONFIG_SOC_SUBFAMILY_STM32F4
    /* On stm32f4, IT0 == Px0, IT1 == Px1, and so on...
     * meaning that io pin (upto 15) define the associated EXTI line
     */
    status = exti_unmask_event(iopin);
#endif
    return status;
}

kstatus_t mgr_io_clear_pending_interrupt(uint8_t ioport, uint8_t iopin)
{
    kstatus_t status = K_STATUS_OKAY;
#ifdef CONFIG_SOC_SUBFAMILY_STM32F4
    /* On stm32f4, IT0 == Px0, IT1 == Px1, and so on...
     * meaning that io pin (upto 15) define the associated EXTI line
     */
    status = exti_clear_pending(iopin);
#endif
    return status;
}
