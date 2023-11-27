// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef SENTRY_HANDLE_H
#define SENTRY_HANDLE_H

#include <sentry/arch/asm-cortex-m/platform.h>
#include <sentry/arch/asm-cortex-m/buses.h>
#include <sentry/arch/asm-cortex-m/irq_defs.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include <uapi/handle.h>

/*@
  // the following predicates can be used until the handle sanitation has been made
  // the goal is to use them until the syscall argument sanitation is done in the
  // kernel code, so that all handler-passed values are formally verified along
  // its usage.
  // These predicates also help with function contracts and assertions

  // gpio handle specification. It requires two const (or macros) defining current
  // number of GPIO ports and current platform pins per port.
  // by now, the id (handle identifier) is not checked
  prediate handle_ioh_is_valid(ioh_t h) =
    h.ioport <= PLATFORM_GPIO_PORT_NUM &&
    h.iopin  <= PLATFORM_GPIO_PIN_NUM &&
    h.reserved == 0 &&
    h.family == HANDLE_IO;

  // this preficate check that the interrupt handle
  predicate handle_inth_is_valid(inth_t h) =
    h.irqn <= __NVIC_VECTOR_LEN &&
    h.reserved == 0 &&
    h.family == HANDLE_INT;
 */

/*
 * Once type is converted from raw register u32 value to typed handle value,
 * generic API is defined that allow optimized backend selection
 */
#define handle_exists(T) _Generic((T),  \
              taskh_t: mgr_task_handle_exists,  \
        ) (T)
#endif


#endif/*!SENTRY_HANDLE_H*/
