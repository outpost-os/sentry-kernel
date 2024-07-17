// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef HANDLER_H
#define HANDLER_H

#include <sentry/arch/asm-generic/thread.h>

/**
 * @brief Arch-specific implementation of the panic() function
 *
 * This function be called anywhere, anytime, and is resonsible for execute the
 * panic triggered functions (TBD)
 * Do **not** return.
 */
/*@
  // the unterminated loop here is kept as this is a panic() function
  assigns \nothing;
 */
static inline __attribute__((noreturn)) void __do_panic(void) {
    /* XXX: here, a security policy should be considered. The do_panic() should call security manager
      primitive (potential cleanups) and other things to define */
#ifndef __FRAMAC__
#if defined(CONFIG_WITH_JTAG_CONNECTED)
    /* explicit breakpoint in jtag mode (JTAG connected) s*/
    asm volatile("bkpt");
#endif
#endif/*__FRAMAC__*/
    do {
#ifndef __FRAMAC__
        asm volatile("nop");
#endif
    } while (1);
}

#ifdef __FRAMAC__
stack_frame_t *svc_handler(stack_frame_t *frame);
#endif

#endif/*HANDLER_H*/
