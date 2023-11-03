// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef HANDLE_H
#define HANDLE_H

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

/**
 * @file Sentry handles specification.
 *
 * All handles are dynamically forged, mostly from DTS files, and handle opaques
 * are uint32_t values with subsets.
 * Handles are unique on the system.
 *
 * All handle-associated objects are stored in generated tables, based on
 * the project dtsi files parsing.
 * these tables are under the responsavility of each object manager
 * (e.g. task manager, device manager, etc.) and manipulating each element
 * identified by the handle is done through the manager kernel-wide API.
 *
 * @info: such model ensure that each manager table storage is local to the manager.
 *  This make the storage structure, field evolution, etc. opaque to all others
 *  kernel modules. Moreover, this allows to avoid any kernel pointer usage.
 *
 * @info: as some actions may require high reactivity, table lookup should be
 * avoided if not needed. To do so, each handle store some usefull informations
 * that can be directly used by the target service, until the handle existance
 * (integrity check) is made. For e.g. setting a GPIO pin do not need to get back
 * the io manager information using the ioh_t argument, as the gpio port and
 * pin is already hardcoded in the ioh_t specific part of the handler.
 */

typedef enum handle_type {
  HANDLE_TASKID = 0,
  HANDLE_DEVICE = 1,
  HANDLE_IO     = 2,
  HANDLE_IRQ    = 3,
  HANDLE_EXTI   = 4,
  HANDLE_DMA    = 5,
  HANDLE_SHM    = 6,
  HANDLE_CLK    = 7,
} handle_type_t;


#define HANDLE_ID_SHIFT         13UL
#define HANDLE_ID_MASK          0x7fff8000UL

#define HANDLE_FAMILLY_SHIFT    29UL
#define HANDLE_FAMILLY_MASK     0xe0000000UL

/* handle_specific field definition. This field depend on the handle_familly */


typedef struct __attribute__((packed)) device_handle {
    unsigned int dev_cap  : 8; /* device required dev-capabilities (mask) */
    unsigned int reserved : 5;
    unsigned int id       : 16; /* unique id for current handle (current device, task, etc) */
    unsigned int familly  : 3;
} devh_t;
static_assert(sizeof(devh_t) == sizeof(uint32_t), "invalid devh_t opaque size");

typedef struct __attribute__((packed)) task_handle {
    unsigned int rerun    : 13; /* current spawn id (start with 1) */
    unsigned int id       : 16; /* unique id for current handle (current device, task, etc) */
    unsigned int familly  : 3;
} taskh_t;
static_assert(sizeof(taskh_t) == sizeof(uint32_t), "invalid taskh_t opaque size");


#define HANDLE_TASK_RERUN_SHIFT 0UL
#define HANDLE_TASK_RERUN_MASK  0x00001fffUL

typedef struct __attribute__((packed))  io_handle {
    unsigned int ioport   : 6; /* 0=A, 1=B...*/
    unsigned int iopin    : 6; /* 0=0, 1=1, ... */
    unsigned int reserved : 1;
    /* this part is fixed */
    unsigned int id       : 16; /* unique id for current handle (current device, task, etc) */
    unsigned int familly  : 3;
} ioh_t;
static_assert(sizeof(ioh_t) == sizeof(uint32_t), "invalid ioh_t opaque size");

typedef struct irq_handle {
    unsigned int irqn     : 8; /* IRQ Number */
    unsigned int reserved : 5;
    unsigned int id       : 16; /* unique id for current handle (current device, task, etc) */
    unsigned int familly  : 3;
} irqh_t;
static_assert(sizeof(irqh_t) == sizeof(uint32_t), "invalid irqh_t opaque size");

typedef struct clk_handle {
    unsigned int bus_id   : 4; /* << 2 to get offset from first clken reg */
    unsigned int clk_id   : 5; /* clken bit */
    unsigned int reserved : 4;
    unsigned int id       : 16; /* unique id for current handle (current device, task, etc) */
    unsigned int familly  : 3;
} clkh_t;
static_assert(sizeof(clkh_t) == sizeof(uint32_t), "invalid clkh_t opaque size");

/**
 * In order to support handle manipulation as raw uint32 (masking, shifting....)
 * a union is defined so that bitfields can ba manipulated with processor
 * optimized mask/shift
 * MUST be used only in local-function part to content framaC.
 */
union u_handle {
    uint32_t val;
    taskh_t  taskh;
    devh_t   devh;
    ioh_t    ioh;
    irqh_t   irqh;
    clkh_t   clkh;
};

#if 0
/*
 * Once type is converted from raw register u32 value to typed handle value,
 * generic API is defined that allow optimized backend selection
 */
#define check_handle_exists(T) _Generic((T),  \
              irqh_t: irqmgr_handle_exists,   \
              clkh_t: clkmgr_handle_exists,   \
              ioh_t:  iomgr_handle_exists,    \
              taskh_t:taskmgr_handle_exists,  \
              devh_t: devmgr_handle_exists    \
        ) (T)
#endif


#endif/*HANDLE_H*/
