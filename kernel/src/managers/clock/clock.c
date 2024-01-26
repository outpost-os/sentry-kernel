// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/managers/clock.h>
#include <sentry/managers/device.h>
#include <sentry/managers/debug.h>
#include <sentry/ktypes.h>

#include <bsp/drivers/clk/rcc.h>
#include <bsp/drivers/clk/pwr.h>
#include <bsp/drivers/flash/flash.h>
#include "perfo.h"

/*
 * Fixme:
 * All of these are tightly coupled and interaction and/or order
 * may vary from one soc to another.
 */
kstatus_t mgr_clock_init(void)
{
    kstatus_t status;
    status = pwr_probe();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }
    status = flash_probe();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }
    status = rcc_probe();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto end;
    }
    status = perfo_init();
end:
    return status;
}

/**
 * @brief enable input clock for device identified by dev
 *
 * CAUTION: no device specific latency before access is added to this function.
 * Depending on the device, some Twaits may be required by the caller. Most
 * of the time, these twaits are very short and the call sequence is enough, but
 * for some specific low frequency devices, this may require some longer wait.
 * This action is left to the device holder (typically the userspace driver)
 *
 * See the corresponding device datasheet for more information.
 *
 * @param[in] dev: device handler, uniquely identify the device on the system
 *
 * @return
 *  K_ERROR_NOENT if the device is not found in the device list
 *  K_STATUS_OKAY if the device is clocked
 */
kstatus_t mgr_clock_enable_device(devh_t dev)
{
    kstatus_t status;
    uint32_t clkid;
    uint32_t busid;
    if (unlikely((status = mgr_device_get_clock_config(dev, &clkid, &busid)) != K_STATUS_OKAY)) {
        pr_err("failed to get back dev %x clocks", dev);
        goto err;
    }
    status = rcc_enable(busid, clkid, RCC_NOFLAG);
err:
    return status;
}

/**
 * @brief disable input clock for device identified by dev
 *
 * @param[in] dev: device handler, uniquely identify the device on the system
 *
 * @return
 *  K_ERROR_NOENT if the device is not found in the device list
 *  K_STATUS_OKAY if the device input clock is disabled
 */
kstatus_t mgr_clock_disable_device(devh_t dev)
{
    kstatus_t status = K_ERROR_INVPARAM;
    uint32_t clkid;
    uint32_t busid;
    if (unlikely((status = mgr_device_get_clock_config(dev, &clkid, &busid)) != K_STATUS_OKAY)) {
        pr_err("failed to get back dev %x clocks", dev);
        goto err;
    }
    status = rcc_disable(busid, clkid, RCC_NOFLAG);
err:
    return status;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_clock_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif
