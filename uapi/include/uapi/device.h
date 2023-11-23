// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef UAPI_DEVICE_H
#define UAPI_DEVICE_H

#include <assert.h>
#include <inttypes.h>
#include <stddef.h>
#include <uapi/handle.h>


/** device information UAPI types. Variables are jinja-generated from dts */

typedef int (*it_handler_p)(uint8_t it);

typedef struct it_info {
    uint8_t      it_controler; /**< interrupt controler identifier */
    uint8_t      it_num;     /**< interrupt number */
    it_handler_p it_handler; /**< interrupt handler, ignored in kernel, used in userspace driver */
} it_info_t;

typedef struct io_info {
    uint8_t      port;   /**< GPIO port identifier, declared in DTS */
    uint8_t      pin;    /**< GPIO pin identifier, declared in DTS */
    uint32_t     config; /**< GPIO pin configuration (dt-binding based bitfield, declared in DTS) */
} io_info_t;


/**
 * @brief userspace oriented device definition
 *
 * In Outpost is device is
 */
typedef struct devinfo {
    devh_t handle;
    bool   mappable;        /**< mappable device. Direct-IO (LED...) are not */
    size_t baseaddr;        /**< for mappable devices, base address */
    size_t size;            /**< for mappable devices, mapped size */
    /**<
     *  number of device's interrupt.
     *  Can be EXTI (button) or NVIC interrupts (SoC device)
     */
    uint8_t num_interrupt;
    it_info_t its[8];       /**< device interrupt list */
    uint8_t num_ios;        /**< number of device I/O (pinmux) */
    io_info_t ios[8];       /**< device I/O list */
} devinfo_t;


#endif/*UAPI_DEVICE_H*/
