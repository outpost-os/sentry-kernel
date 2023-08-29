// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ARM_SYSTEM_H
#define ARM_SYSTEM_H

/**
 * \file ARM system layout definition (ARM standard)
 */

/*
 * ARM defines all the ARMv7M related system component mapping
 * They are all mapped in a predefined address for all SoCs
 */

#define SYSMEM_BASE     0xE0000000u
#define NVIC_STIR_BASE (SCS_BASE + 0xf00u)   /* NVIC_STIR Base Address   */

#define SYSTICK_BASE  (SCS_BASE + 0x010u)   /* SysTick Base Address      */


#if defined(CONFIG_HAS_FPU) && (CONFIG_HAS_FPU == 1)
# define __FPU_PRESENT 1U
#endif

#if defined(CONFIG_USE_FPU) && (CONFIG_USE_FPU == 1)
#  if defined(CONFIG_FPV5_SP) && (CONFIG_FPV5_SP == 1)
#   define __FPU_DP 0U
#  elif defined(CONFIG_FPV5_DP) && (CONFIG_FPV5_DP == 1)
#   define __FPU_DP 1U
#  else
#   error "Configuration must select one of these (CONFIG_FPV5_SP/CONFIG_FPV5_DP)"
#  endif
#endif

#if defined (CONFIG_HAS_MPU) && (CONFIG_HAS_MPU == 1)
# define __MPU_PRESENT 1U
#endif


/* NVIC related content */
#if defined(CONFIG_HAS_NVIC) && (CONFIG_HAS_NVIC == 1)

#include <arch/asm-generic/interrupt.h>
/* including CMSIS headers*/

#ifdef CONFIG_ARCH_ARM_CORTEX_M3
#include <cmsis/core_cm3.h>
#elif defined(CONFIG_ARCH_ARM_CORTEX_M4)
#include <cmsis/core_cm4.h>
#elif defined(CONFIG_ARCH_ARM_CORTEX_M7)
#include <cmsis/core_cm7.h>
#elif defined(CONFIG_ARCH_ARM_CORTEX_M33)
#include <cmsis/core_cm33.h>
#else
#error "unsupported Cortex-M platform"
#endif


#include <assert.h>

/*
 * include kconfig generated header autoconfig.h
 * forge variables for CMSIS configuration
 * include corresponding CMSIS arch header
 *
 * TODO: stub in FramaC context !?!
 */

#define ARMV7M_MIN_NVIC_PRIO_BITS 3
#define ARMV7M_MAX_NVIC_PRIO_BITS 8


# define __VTOR_PRESENT 1U

static_assert(__NVIC_PRIO_BITS >= ARMV7M_MIN_NVIC_PRIO_BITS, "priobits must be at least 3");
static_assert(__NVIC_PRIO_BITS <= ARMV7M_MAX_NVIC_PRIO_BITS, "priobits must be at most 8");


/* Instruction Cache present */
#if defined(CONFIG_HAS_ICACHE) && (CONFIG_HAS_ICACHE == 1)
#  define __ICACHE_PRESENT 1U
#endif

/* Data Cache present */
#if defined(CONFIG_HAS_DCACHE) && (CONFIG_HAS_DCACHE == 1)
#  define __DCACHE_PRESENT 1U
#endif

#endif

#endif/*!ARM_SYSTEM_H*/
