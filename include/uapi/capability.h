// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef UAPI_CAPABILITY_H
#define UAPI_CAPABILITY_H

/**
 * Capabilities are encoded as a bitmask, with the following register-like structure:
 *  [ reserved ][ other capa ][ mem ][ sys capa ][ dev capa ]
 *  31        25,24        20,19  16,15        12,11        0
 *
 * this allows dev handle to hold the associated dev capa
 */
typedef enum sentry_capability {
    CAP_DEV_BUSES        = 0x000001UL, /**< access to resources tagged as buses (uart, spi, i2c, sai controllers...), include IO */
    CAP_DEV_IO           = 0x000002UL, /**< access to external SoC I/O (GPIO access and EXTI typically) */
    CAP_DEV_DMA          = 0x000004UL, /**< access to DMA streams API */
    CAP_DEV_ANALOG       = 0x000008UL, /**< access to analogic-related devices (ADC, DAC... */
    CAP_DEV_TIMER        = 0x000010UL, /**< access to timers and RTC resources */
    CAP_DEV_STORAGE      = 0x000020UL, /**< access to local storage */
    CAP_DEV_CRYPTO       = 0x000040UL, /**< access to cryptographic-related devices (crypto accelerator, hmac...), that are allowed to userspace */
    CAP_DEV_CLOCK        = 0x000080UL, /**< access to local clock source (RTC...) */
    CAP_DEV_POWER        = 0x000100UL, /**< access to a power device (battery, USB-C PD...) */
    CAP_DEV_NEURAL       = 0x000200UL, /**< access to a neural or AI related device */
    CAP_SYS_UPGRADE      = 0x001000UL,/**< access to upgrade-related objects, including local storage, crypo-related API, and reset request, etc. */
    CAP_SYS_POWER        = 0X002000UL, /**< access to power-management interface (moving to and from sleep mode for e.g.) */
    CAP_SYS_PROCSTART    = 0X004000UL, /**< can start another process */
    CAP_MEM_SHM_OWN      = 0x010000UL, /**< can own a shared memory */
    CAP_MEM_SHM_USE      = 0x020000UL, /**< can use another task's owned shared memory, while other has allowed it in SHM's perms */
    CAP_MEM_SHM_TRANSFER = 0x040000UL, /**< can transfer another task's owned shared memory usage while other has allowed it, but without accessing it */
    CAP_TIM_HP_CHRONO    = 0x100000UL, /**< access to accurate time measurements objects from kernel */
    CAP_CRY_KRNG         = 0x200000UL, /**< access to kernel entropy source. Kernel entropy source quality (and compliance) is project-dependent */
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
