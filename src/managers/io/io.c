// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry I/O manager
 */

#include <sentry/ktypes.h>
#include <sentry/driver/gpio/gpio.h>
#ifdef CONFIG_SOC_FAMILY_STM32
#include <sentry/driver/exti/exti.h>
#endif
#include <sentry/managers/io.h>

#include <uapi/handle.h>

/**
 * @brief probe all BSP-related part of the I/O manipulation
 *
 * Kconfig already has auto-selected the various drviers needed for I/O. All
 * I/O drivers probing and manipulation is done through this manager's API.
 */
kstatus_t io_probe(void)
{
    kstatus_t status = K_STATUS_OKAY;

    /* This backend should be generic to any SoC, any arch */
    if (unlikely((status = gpio_probe()) != K_STATUS_OKAY) {
        goto err;
    };
#ifdef CONFIG_SOC_FAMILY_STM32
    /* STM32 BSP implement EXTI controler for external interrupt & events */
    if (unlikely((status = exti_probe()) != K_STATUS_OKAY) {
        goto err;
    };
#endif
err:
    return status;
}

/**
 * @brief Set I/O identified by ioh
 *
 * This set output moode I/O line value to high level
 */
kstatus_t io_set(ioh_t ioh)
{

}

/**
 * @brief Reset I/O identified by ioh
 *
 * This set output moode I/O line value to low level
 */
kstatus_t io_reset(ioh_t ioh)
{

}

/**
 * @brief Read I/O identified by ioh
 *
 * This get back current I/O line value, in both INPUT and OUTPUT mode
 */
kstatus_t io_read(ioh_t ioh, bool *val)
{

}

/**
 * @brief Configure I/O identified by ioh
 */
kstatus_t io_configure(ioh_t ioh)
{

}

/* About interrupt associated to I/O */


kstatus_t io_mask_interrupt(ioh_t ioh)
{

}

kstatus_t io_unmask_interrupt(ioh_t ioh)
{

}

kstatus_t io_mask_event(ioh_t ioh)
{

}

kstatus_t io_unmask_event(ioh_t ioh)
{

}

kstatus_t io_clear_pending_interrupt(ioh_t ioh)
{

}
