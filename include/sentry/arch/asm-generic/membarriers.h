// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file membarriers entrypoint, multiplatform
 */

#ifdef CONFIG_ARCH_ARM_CORTEX_M
#include <sentry/arch/asm-cortex-m/membarriers.h>
#else
#error "unsupported architecture!"
#endif
