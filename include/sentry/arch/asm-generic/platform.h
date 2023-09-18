// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef PLATFORM_H
#define PLATFORM_H
/**
 * \file platform initialisation, portable API
 */

#include <stdbool.h>

#ifdef CONFIG_ARCH_ARM_CORTEX_M
#include <sentry/arch/asm-cortex-m/platform.h>
#else
#error "unsupported architecture!"
#endif

/**
 * finalize platform early initialization (NVIC, power, potential dirty boot state)
 */
void platform_init(void);

/**
 * Check if platform init is done (typically for interrupt handlers)
 */
bool platform_is_init_done(void);

#endif/*!PLATFORM_H*/
