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
  HANDLE_IPC    = 4,
  HANDLE_DMA    = 5,
  HANDLE_SHM    = 6,
  HANDLE_SIGNAL = 7,
} handle_type_t;


#define HANDLE_ID_SHIFT         13UL
#define HANDLE_ID_MASK          0x7fff8000UL

#define HANDLE_FAMILLY_SHIFT    29UL
#define HANDLE_FAMILLY_MASK     0xe0000000UL

/* handle_specific field definition. This field depend on the handle_family */


typedef struct __attribute__((packed)) signal_handle {
    unsigned int source   : 16;
    unsigned int id       : 13; /* unique id for current handle (current device, task, etc) */
    unsigned int family  : 3;
} sigh_t;
static_assert(sizeof(sigh_t) == sizeof(uint32_t), "invalid sigh_t opaque size");


typedef struct __attribute__((packed)) ipc_handle {
    unsigned int source   : 16; /* IPC source (task label) */
    unsigned int len      : 13; /* IPC len in bytes */
    unsigned int family  : 3;
} ipch_t;
static_assert(sizeof(ipch_t) == sizeof(uint32_t), "invalid ipch_t opaque size");

typedef struct __attribute__((packed)) device_handle {
    unsigned int dev_cap  : 12; /* device required dev-capabilities (mask) */
    unsigned int reserved : 1;
    unsigned int id       : 16; /* unique id for current handle (current device, task, etc) */
    unsigned int family  : 3;
} devh_t;

static_assert(sizeof(devh_t) == sizeof(uint32_t), "invalid devh_t opaque size");

typedef struct __attribute__((packed)) task_handle {
    unsigned int rerun    : 13; /* current spawn id (start with 1) */
    unsigned int id       : 16; /* unique id for current handle (current device, task, etc) */
    unsigned int family  : 3;
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
    unsigned int family  : 3;
} ioh_t;
static_assert(sizeof(ioh_t) == sizeof(uint32_t), "invalid ioh_t opaque size");

typedef struct irq_handle {
    unsigned int irqn     : 8; /* IRQ Number */
    unsigned int reserved : 5;
    unsigned int id       : 16; /* unique id for current handle (current device, task, etc) */
    unsigned int family  : 3;
} irqh_t;
static_assert(sizeof(irqh_t) == sizeof(uint32_t), "invalid irqh_t opaque size");

typedef struct shm_handle {
    unsigned int reserved : 13; /* TODO define reserved content */
    unsigned int id       : 16; /* unique id for current handle (current device, task, etc) */
    unsigned int familly  : 3;
} shmh_t;
static_assert(sizeof(shmh_t) == sizeof(uint32_t), "invalid shmh_t opaque size");

typedef struct dma_handle {
    unsigned int reserved : 13; /* TODO define reserved content */
    unsigned int id       : 16; /* unique id for current handle (current device, task, etc) */
    unsigned int familly  : 3;
} dmah_t;
static_assert(sizeof(dmah_t) == sizeof(uint32_t), "invalid dmah_t opaque size");

/**
 * utility tooling for u32<->handles translation, using generic.
 * Please use the Genric api, not the specialized macros
 */
static inline uint32_t handle_convert_irqh_to_u32(irqh_t h) {
    return (uint32_t)(((h.id << HANDLE_ID_SHIFT) & HANDLE_ID_MASK) |
               ((h.family << HANDLE_FAMILLY_SHIFT) & HANDLE_FAMILLY_MASK) |
               (h.irqn & 0xffUL));
}

static inline uint32_t handle_convert_ioh_to_u32(ioh_t h) {
    return (uint32_t)(((h.id << HANDLE_ID_SHIFT) & HANDLE_ID_MASK) |
               ((h.family << HANDLE_FAMILLY_SHIFT) & HANDLE_FAMILLY_MASK) |
               ((h.iopin << 6UL) & 0xfc0UL) |
               (h.ioport & 0x3fUL));
}

static inline uint32_t handle_convert_taskh_to_u32(taskh_t h) {
    return (uint32_t)(((h.id << HANDLE_ID_SHIFT) & HANDLE_ID_MASK) |
               ((h.family << HANDLE_FAMILLY_SHIFT) & HANDLE_FAMILLY_MASK) |
               (h.rerun & 0x1fffUL));
}

static inline uint32_t handle_convert_shmh_to_u32(shmh_t h) {
    return (uint32_t)(((h.id << HANDLE_ID_SHIFT) & HANDLE_ID_MASK) |
               ((h.familly << HANDLE_FAMILLY_SHIFT) & HANDLE_FAMILLY_MASK) |
               (h.reserved & 0xfff1UL));
}

static inline uint32_t handle_convert_devh_to_u32(devh_t h) {
    return (uint32_t)(((h.id << HANDLE_ID_SHIFT) & HANDLE_ID_MASK) |
               ((h.family << HANDLE_FAMILLY_SHIFT) & HANDLE_FAMILLY_MASK) |
               (h.dev_cap & 0xfffUL));
}

static inline uint32_t handle_convert_dmah_to_u32(devh_t h) {
    return (uint32_t)(((h.id << HANDLE_ID_SHIFT) & HANDLE_ID_MASK) |
               ((h.familly << HANDLE_FAMILLY_SHIFT) & HANDLE_FAMILLY_MASK) |
               (h.dev_cap & 0xfffUL));
}

#define handle_convert_to_u32(T) _Generic((T),  \
              irqh_t:  handle_convert_irqh_to_u32,   \
              ioh_t:   handle_convert_ioh_to_u32,    \
              taskh_t: handle_convert_taskh_to_u32,  \
              devh_t:  handle_convert_devh_to_u32,   \
              shmh_t:  handle_convert_shmh_to_u32,   \
              dmah_t:  handle_convert_dmah_to_u32    \
        ) (T)


#endif/*HANDLE_H*/
