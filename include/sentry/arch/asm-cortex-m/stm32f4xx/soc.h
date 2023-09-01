// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef STM32F4XX_SOC_H_
#define STM32F4XX_SOC_H_

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

#endif/*STM32F4_SOC_H_*/
