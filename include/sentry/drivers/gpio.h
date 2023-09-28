// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file I/O manipulation primitive
 */

#ifndef GPIO_H
#define GPIO_H

/**
 * \file Generic, portable, API for GPIO drivers. Should be kept the same for
 * various platforms
 */

typedef enum gpio_mode {
    GPIOx_MODE_INPUT     = 0x0UL,
    GPIOx_MODE_OUT       = 0x1UL,
    GPIOx_MODE_AF        = 0x2UL,
    GPIOx_MODE_ANALOG    = 0x3UL,
} gpio_mode_t;

typedef enum gpio_type {
    GPIOx_TYPE_PPULL     = 0x0UL,
    GPIOx_TYPE_OPENDRAIN = 0x1UL,
} gpio_type_t;

typedef enum gpio_speed {
    GPIOx_SPEED_LOW       = 0x0UL,
    GPIOx_SPEED_MEDIUM    = 0x1UL,
    GPIOx_SPEED_HIGH      = 0x2UL,
    GPIOx_SPEED_VERY_HIGH = 0x3UL,
} gpio_speed_t;


typedef enum gpio_pullupd {
    GPIOx_NOPULL    = 0x0UL,
    GPIOx_PULLUP    = 0x1UL,
    GPIOx_PULLDOWN  = 0x2UL,
} gpio_pullupd_t;

size_t gpio_get_controller_address(char controller);

sentry_error_t gpio_set_mode(size_t gpio_port_address, uint8_t pin, gpio_mode_t mode);
sentry_error_t gpio_set_type(size_t gpio_port_address, uint8_t pin, gpio_type_t type);

#endif/*!GPIO_H*/
