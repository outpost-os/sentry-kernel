// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file thread context manipulation entrypoint, multiplatform
 */

#ifdef CONFIG_ARCH_CORTEX_M
#include <arch/asm-cortex-m/thread.h>
#else
#error "unsupported architecture!"
#endif
