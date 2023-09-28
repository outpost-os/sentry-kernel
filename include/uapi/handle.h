// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef HANDLE_H
#define HANDLE_H

#include <assert.h>

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

typedef enum {
  HANDLE_TASKID = 0,
  HANDLE_DEVICE = 1,
  HANDLE_IO     = 2,
  HANDLE_IRQ    = 3,
  HANDLE_EXTI   = 4,
  HANDLE_DMA    = 5,
  HANDLE_SHM    = 6,
  HANDLE_CLK    = 7,
}

/* handle_specific field definition. This field depend on the handle_familly */

/**
 * An I/O is something 'easy', it is a gpio pin/port couple.
 * This information is encoded in the handle
 */
struct __attribute__((packed)) handle_specific_io {
    uint32_t ioport: 4; /* 0=A, 1=B...*/
    uint32_t iopin: 4; /* 0=0, 1=1, ... */
    uint32_t reserved: 5;
};

/**
 * task identifier specific
 */
struct __attribute__((packed)) handle_specific_task {
    uint32_t rerun: 13; /* current spawn id (start with 1) */
};

/**
 * mappable device specific
 */
struct __attribute__((packed)) handle_specific_dev {
    uint32_t dev_cap: 8; /* device required dev-capabilities (mask) */
    uint32_t reserved: 5;
};

struct __attribute__((packed)) handle_specific_irq {
    uint32_t irqn: 8; /* IRQ Number */
    uint32_t reserved: 5;
};

struct __attribute__((packed)) handle_specific_shm {
    uint32_t reserved: 13;
};


/**
 * @brief clock specific metadata hold in the clock handle
 *
 * Clock handle is manipulated at kernel level only.
 *
 */
struct __attribute__((packed)) handle_specific_clk {
    uint32_t bus_id: 4; /* << 2 to get offset from first clken reg */
    uint32_t clk_id: 5; /* clken bit */
    uint32_t reserved: 4;
};

typedef struct device_handle {
   struct handle_specific_dev specific : 13;
   uint32_t                   id       : 16; /* unique id for current handle (current device, task, etc) */
   uint32_t                   familly  : 3;
} devh_t;
static_assert(sizeof(devh_t) == sizeof(uint32_t), "invalid devh_t opaque size");

typedef struct task_handle {
   struct handle_specific_task specific : 13;
   uint32_t                    id       : 16; /* unique id for current handle (current device, task, etc) */
   uint32_t                    familly  : 3;
} taskh_t;
static_assert(sizeof(taskh_t) == sizeof(uint32_t), "invalid taskh_t opaque size");

typedef struct io_handle {
   struct handle_specific_io  specific : 13;
   uint32_t                   id       : 16; /* unique id for current handle (current device, task, etc) */
   uint32_t                   familly  : 3;
} ioh_t;
static_assert(sizeof(ioh_t) == sizeof(uint32_t), "invalid ioh_t opaque size");

typedef struct irq_handle {
   struct handle_specific_irq specific : 13;
   uint32_t                   id       : 16; /* unique id for current handle (current device, task, etc) */
   uint32_t                   familly  : 3;
} irqh_t;
static_assert(sizeof(irqh_t) == sizeof(uint32_t), "invalid irqh_t opaque size");

typedef struct clk_handle {
   struct handle_specific_clk specific : 13;
   uint32_t                   id       : 16; /* unique id for current handle (current device, task, etc) */
   uint32_t                   familly  : 3;
} clkh_t;
static_assert(sizeof(clkh_t) == sizeof(uint32_t), "invalid clkh_t opaque size");

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

#endif/*HANDLE_H*/
