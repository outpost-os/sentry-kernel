// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef THREAD_H
#define THREAD_H
/**
 * \file thread context manipulation entrypoint, multiplatform
 */

#ifdef CONFIG_ARCH_ARM_CORTEX_M
#include <sentry/arch/asm-cortex-m/thread.h>
#else
#error "unsupported architecture!"
#endif

/**
 * kernel thread type definition
 */
typedef int (*kthread_t)(void);

#endif/*THREAD_H*/
