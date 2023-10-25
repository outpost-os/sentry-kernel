// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __SENTRY_BSP_DRIVERS_GPIO_PINCTRL_H
#define __SENTRY_BSP_DRIVERS_GPIO_PINCTRL_H

#include <sentry/ktypes.h>
#include <bsp/drivers/gpio/gpio.h>

typedef struct gpio_pinctrl_desc {
    gpio_mode_t mode;
    gpio_af_t altfunc;
    gpio_type_t type;
    gpio_speed_t speed;
    gpio_pullupd_t pull_mode;
    uint8_t port_id;
    uint8_t pin;
} gpio_pinctrl_desc_t;

kstatus_t gpio_pinctrl_configure(gpio_pinctrl_desc_t pinctrl_desc);

#endif /* __SENTRY_BSP_DRIVERS_GPIO_PINCTRL_H */
