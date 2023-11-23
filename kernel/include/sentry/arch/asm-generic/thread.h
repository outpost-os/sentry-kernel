// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef THREAD_H
#define THREAD_H

/**
 * \file interrupts controller entrypoint, multiplatform
 */

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/thread.h>
#elif defined(__x86_64__)
#include <sentry/arch/asm-x86_64/thread.h>
#elif defined(__i386__)
#include <sentry/arch/asm-i386/thread.h>
#else
#error "unsupported architecture!"
#endif

#endif/*THREAD_H*/
