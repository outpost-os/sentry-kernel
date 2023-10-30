// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef PANIC_H
#define PANIC_H

/**
 * \file interrupts controller entrypoint, multiplatform
 */

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/handler.h>
#elif defined(__x86_64__)
// nothing, userspace mode
#elif defined(__i386__)
// nothing, userspace mode
#else
#error "unsupported architecture!"
#endif

static inline void __attribute__((noreturn)) panic(void) {
#if defined(__arm__) || defined(__FRAMAC__)
    /* calling arch-specific panic handler */
    __do_panic();
#else
    /* INFO: clang auto purge protection:
        when a loop with no external impact and with a constant
        loop trigger is implemented, clang just drop it */
    do {
        asm volatile("": : :"memory");
    } while (1);
#endif
}

#endif/*PANIC_H*/
