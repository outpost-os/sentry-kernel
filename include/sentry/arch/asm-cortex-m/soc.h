// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef SOC_H
#define SOC_H

#if defined(CONFIG_ARCH_MCU_STM32F407)
#include <sentry/arch/asm-cortex-m/stm32f407/soc.h>
#elif defined(CONFIG_ARCH_MCU_STM32F419)
#include <sentry/arch/asm-cortex-m/stm32f419/soc.h>
#elif defined(CONFIG_ARCH_MCU_STM32F429)
#include <sentry/arch/asm-cortex-m/stm32f429/soc.h>
#elif defined(CONFIG_ARCH_MCU_STM32F439)
#include <sentry/arch/asm-cortex-m/stm32f439/soc.h>
#elif defined(CONFIG_ARCH_MCU_STM32WB55)
#include <sentry/arch/asm-cortex-m/stm32wb55/soc.h>
#elif defined(CONFIG_ARCH_MCU_STM32U5)
#include <sentry/arch/asm-cortex-m/stm32u5/soc.h>
#else
#error "unsupported SoC"
#endif

#endif/*!SOC_H*/
