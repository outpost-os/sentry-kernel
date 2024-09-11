// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef INTERRUPT_MANAGER_H
#define INTERRUPT_MANAGER_H

/**
 * @file Sentry Debug manager
 */
#include <sentry/ktypes.h>
#include <sentry/arch/asm-generic/interrupt.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * This is the interrupt handler for IRQ lines associated to ressources that
 * can be declared as userspace ressources (i.e. no exception, no system interrupts)
 */
stack_frame_t *userisr_handler(stack_frame_t *frame, int IRQn);

static inline kstatus_t mgr_interrupt_early_init(void) {
    interrupt_disable();
    interrupt_init();
    return K_STATUS_OKAY;
}

kstatus_t mgr_interrupt_init(void);

kstatus_t mgr_interrupt_enable_irq(uint32_t irq);

kstatus_t mgr_interrupt_disable_irq(uint32_t irq);

kstatus_t mgr_interrupt_acknowledge_irq(uint32_t irq);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_interrupt_autotest(void);
#endif

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif/*!INTERRUPT_MANAGER_H*/
