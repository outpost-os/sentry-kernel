// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file External interrupts and events manipulation primitives
 */

#ifndef EXTI_H
#define EXTI_H

#include <inttypes.h>
#include <sentry/ktypes.h>

kstatus_t exti_probe(void);

kstatus_t exti_mask_interrupt(uint8_t itn);

kstatus_t exti_unmask_interrupt(uint8_t itn);

kstatus_t exti_mask_event(uint8_t evn);

kstatus_t exti_unmask_event(uint8_t evn)

kstatus_t exti_generate_swinterrupt(uint8_t itn);

kstatus_t exti_clear_pending(uint8_t itn);

#endif/* EXTI_H */
