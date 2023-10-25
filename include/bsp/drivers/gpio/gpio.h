// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file I/O manipulation primitive
 */

#ifndef GPIO_H
#define GPIO_H

#include <stdbool.h>
#include <stdint.h>

#include <sentry/ktypes.h>
/**
 * \file Generic, portable, API for GPIO drivers. Should be kept the same for
 * various platforms. For each of theses standard fields, if the HW
 * IP use different value encoding, the value translation must be done
 * at driver level (for e.g. with macros), the driver upper API kept generic.
 */

/**
 * @brief Generic GPIO mode configuration
 */
typedef enum gpio_mode {
    GPIOx_MODE_INPUT     = 0x0UL,
    GPIOx_MODE_OUT       = 0x1UL,
    GPIOx_MODE_AF        = 0x2UL,
    GPIOx_MODE_ANALOG    = 0x3UL,
} gpio_mode_t;

/**
 * @brief Generic GPIO type configuration
 */
typedef enum gpio_type {
    GPIOx_TYPE_PPULL     = 0x0UL,
    GPIOx_TYPE_OPENDRAIN = 0x1UL,
} gpio_type_t;

/**
 * @brief Generic GPIO speed configuration
 */
typedef enum gpio_speed {
    GPIOx_SPEED_LOW       = 0x0UL,
    GPIOx_SPEED_MEDIUM    = 0x1UL,
    GPIOx_SPEED_HIGH      = 0x2UL,
    GPIOx_SPEED_VERY_HIGH = 0x3UL,
} gpio_speed_t;

/**
 * @brief Generic GPIO pull mode configuration
 */
typedef enum gpio_pullupd {
    GPIOx_NOPULL    = 0x0UL,
    GPIOx_PULLUP    = 0x1UL,
    GPIOx_PULLDOWN  = 0x2UL,
} gpio_pullupd_t;

/**
 * @brief generic naming for GPIO alternate function
 *
 * the correct AF value should be a dtsi setting that match the
 * corresponding SoC & board configuration.
 */
typedef enum gpio_af {
    GPIOx_AF_0      = 0x0UL,
    GPIOx_AF_1      = 0x1UL,
    GPIOx_AF_2      = 0x2UL,
    GPIOx_AF_3      = 0x3UL,
    GPIOx_AF_4      = 0x4UL,
    GPIOx_AF_5      = 0x5UL,
    GPIOx_AF_6      = 0x6UL,
    GPIOx_AF_7      = 0x7UL,
    GPIOx_AF_8      = 0x8UL,
    GPIOx_AF_9      = 0x9UL,
    GPIOx_AF_10     = 0xaUL,
    GPIOx_AF_11     = 0xbUL,
    GPIOx_AF_12     = 0xcUL,
    GPIOx_AF_13     = 0xdUL,
    GPIOx_AF_14     = 0xeUL,
    GPIOx_AF_15     = 0xfUL,
} gpio_af_t;

/*
 * GPIO controlers probbing, at boot time
 */
kstatus_t gpio_probe(uint8_t gpio_port_id);

/**
 * Configuration-time API
 */
kstatus_t gpio_set_mode(uint8_t gpio_port_id, uint8_t pin, gpio_mode_t mode);

kstatus_t gpio_set_pull_mode(uint8_t gpio_port_id, uint8_t pin, gpio_pullupd_t pupd);

kstatus_t gpio_set_type(uint8_t gpio_port_id, uint8_t pin, gpio_type_t type);

kstatus_t gpio_set_af(uint8_t gpio_port_id, uint8_t pin, gpio_af_t af);

kstatus_t gpio_set_speed(uint8_t gpio_port_id, uint8_t pin, gpio_speed_t speed);

/*
 * Access-time API
 */
kstatus_t gpio_set(uint8_t gpio_port_id, uint8_t pin);

kstatus_t gpio_reset(uint8_t gpio_port_id, uint8_t pin);

kstatus_t gpio_get(uint8_t gpio_port_id, uint8_t pin, bool *val);

#endif/*!GPIO_H*/
