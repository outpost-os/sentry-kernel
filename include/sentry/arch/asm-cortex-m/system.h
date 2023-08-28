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

#endif/*!ARM_SYSTEM_H*/
