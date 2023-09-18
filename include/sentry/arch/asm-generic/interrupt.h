// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef INTERRUPT_H
#define INTERRUPT_H

/**
 * \file interrupts controller entrypoint, multiplatform
 */

#ifdef CONFIG_ARCH_ARM_CORTEX_M
#include <sentry/arch/asm-cortex-m/nvic.h>
#else
#error "unsupported architecture!"
#endif

#endif/*INTERRUPT_H*/
