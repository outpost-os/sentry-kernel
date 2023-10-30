// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef HANDLER_H
#define HANDLER_H

static inline __attribute__((noreturn)) void __do_panic(void) {
    /* XXX: here, a security policy should be considered. The do_panic() should call security manager
      primitive (potential cleanups) and other things to define */
    do {
        asm volatile("nop");
    } while (1);
}

#endif/*HANDLER_H*/
