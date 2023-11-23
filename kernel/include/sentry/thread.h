// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef THREAD_H
#define THREAD_H
/**
 * \file thread context manipulation entrypoint, multiplatform
 */

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/thread.h>
#elif defined(__x86_64__)
#include <sentry/arch/asm-x86_64/apic.h>
#elif defined(__i386__)
// no include
#else
#error "unsupported architecture!"
#endif
/**
 * kernel thread type definition
 */
typedef int (*kthread_t)(void);

#endif/*THREAD_H*/
