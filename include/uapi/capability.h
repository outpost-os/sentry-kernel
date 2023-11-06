// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef UAPI_CAPABILITY_H
#define UAPI_CAPABILITY_H

/**
 * Capabilities are encoded as a bitmask, with the following register-like structure:
 *  [ other capa ][ mem ][ sys capa ][ dev capa ]
 *  15          14,13  11,10        8,7         0
 *
 * this allows dev handle to hold the associated dev capa
 */
typedef enum sentry_capability {
    CAP_DEV_BUSES        = 0x0001UL, /**< access to resources tagged as buses (uart, spi, i2c, sai controllers...), include IO */
    CAP_DEV_IO           = 0x0002UL, /**< access to external SoC I/O (GPIO access and EXTI typically) */
    CAP_DEV_DMA          = 0x0004UL, /**< access to DMA streams API */
    CAP_DEV_ANALOG       = 0x0008UL, /**< access to analogic-related devices (ADC, DAC... */
    CAP_DEV_TIMER        = 0x0010UL, /**< access to timers and RTC resources */
    CAP_DEV_STORAGE      = 0x0020UL, /**< access to local storage */
    CAP_DEV_CRYPTO       = 0x0040UL, /**< access to cryptographic-related devices (crypto accelerator, hmac...), that are allowed to userspace */
    CAP_DEV_CLOCK        = 0x0080UL, /**< access to local clock source (RTC...) */
    CAP_SYS_UPGRADE      = 0x0100UL,/**< access to upgrade-related objects, including local storage, crypo-related API, and reset request, etc. */
    CAP_SYS_POWER        = 0X0200UL, /**< access to power-management interface (moving to and from sleep mode for e.g.) */
    CAP_SYS_PROCSTART    = 0X0400UL, /**< can start another process */
    CAP_MEM_SHM_OWN      = 0x0800UL, /**< can own a shared memory */
    CAP_MEM_SHM_USE      = 0x1000UL, /**< can use another task's owned shared memory, while other has allowed it in SHM's perms */
    CAP_MEM_SHM_TRANSFER = 0x1000UL, /**< can transfer another task's owned shared memory usage while other has allowed it, but without accessing it */
    CAP_TIM_HP_CHRONO    = 0x4000UL, /**< access to accurate time measurements objects from kernel */
    CAP_CRY_KRNG         = 0x8000UL, /**< access to kernel entropy source. Kernel entropy source quality (and compliance) is project-dependent */
} sentry_capability_t;


/**
 * Very short helper macros for basic capability check
 */
#define HAS_DEV_BUSES_CAPABILITY(l)        ((l) & CAP_DEV_BUSES)
#define HAS_DEV_IO_CAPABILITY(l)           ((l) & CAP_DEV_IO)
#define HAS_DEV_DMA_CAPABILITY(l)          ((l) & CAP_DEV_DMA)
#define HAS_DEV_ANALOG_CAPABILITY(l)       ((l) & CAP_DEV_ANALOG)
#define HAS_DEV_TIMER_CAPABILITY(l)        ((l) & CAP_DEV_TIMER)
#define HAS_DEV_STORAGE_CAPABILITY(l)      ((l) & CAP_DEV_STORAGE)
#define HAS_DEV_CRYPTO_CAPABILITY(l)       ((l) & CAP_DEV_CRYPTO)
#define HAS_DEV_CLOCK_CAPABILITY(l)        ((l) & CAP_DEV_CLOCK)
#define HAS_SYS_UPGRADE_CAPABILITY(l)      ((l) & CAP_SYS_UPGRADE)
#define HAS_SYS_POWER_CAPABILITY(l)        ((l) & CAP_SYS_POWER)
#define HAS_SYS_PROCSTART_CAPABILITY(l)    ((l) & CAP_SYS_PROCSTART)
#define HAS_MEM_SHM_OWN_CAPABILITY(l)      ((l) & CAP_MEM_SHM_OWN)
#define HAS_MEM_SHM_USE_CAPABILITY(l)      ((l) & CAP_MEM_SHM_USE)
#define HAS_MEM_SHM_TRANSFER_CAPABILITY(l) ((l) & CAP_MEM_SHM_TRANSFER)
#define HAS_TIM_HP_CHRONO_CAPABILITY(l)    ((l) & CAP_TIM_HP_CHRONO)
#define HAS_CRY_KRNG_CAPABILITY(l)         ((l) & CAP_CRY_KRNG)

#endif/*!UAPI_CAPABILITY_H*/
