// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef STM32F4XX_SOC_H_
#define STM32F4XX_SOC_H_

#include <assert.h>
#include "irq.h"
/**
 * \file basic mapping informations that can be used by STM32F4xx drivers
 */
#define PERIPH_BASE           (0x40000000UL) /* Peripheral Base Address  */
#define APB1PERIPH_BASE       PERIPH_BASE
#define APB2PERIPH_BASE       (PERIPH_BASE + 0x00010000)
#define AHB1PERIPH_BASE       (PERIPH_BASE + 0x00020000)
#define AHB2PERIPH_BASE       (PERIPH_BASE + 0x10000000)

#define PERIPH_BASE_BITBANG1_BASE           (0x40000000UL) /* From 0x40000000UL to 0x400FFFFFUL */
#define PERIPH_BASE_BITBANG2_BASE           (0x42000000UL) /* From 0x42000000UL to 0x43FFFFFFUL */

#define ARMV7M_MIN_NVIC_PRIO_BITS 3
#define ARMV7M_MAX_NVIC_PRIO_BITS 8


# define __VTOR_PRESENT 1U



/* Instruction Cache present */
#if defined(CONFIG_HAS_ICACHE) && (CONFIG_HAS_ICACHE == 1)
#  define __ICACHE_PRESENT 1U
#endif

/* Data Cache present */
#if defined(CONFIG_HAS_DCACHE) && (CONFIG_HAS_DCACHE == 1)
#  define __DCACHE_PRESENT 1U
#endif

/*
 * ARM defines all the ARMv7M related system component mapping
 * They are all mapped in a predefined address for all SoCs
 */
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

#include <cmsis/core_cm4.h>
/* SCS_BASE defined by CMSIS */

#define NVIC_STIR_BASE (SCS_BASE + 0xf00u)   /* NVIC_STIR Base Address   */

#define SYSTICK_BASE  (SCS_BASE + 0x010u)   /* SysTick Base Address      */



static_assert(__NVIC_PRIO_BITS >= ARMV7M_MIN_NVIC_PRIO_BITS, "priobits must be at least 3");
static_assert(__NVIC_PRIO_BITS <= ARMV7M_MAX_NVIC_PRIO_BITS, "priobits must be at most 8");


#endif/*STM32F4_SOC_H_*/
