// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef NVIC_H
#define NVIC_H

#include <stddef.h>
#include <sentry/ktypes.h>
#include <sentry/arch/asm-cortex-m/membarriers.h>
#ifdef __FRAMAC__
/** NOTE: SCB base addresses are required for contracts */
#include <sentry/arch/asm-cortex-m/scb.h>
#endif

#include "soc.h"

#ifdef CONFIG_ARCH_ARM_ARMV8M
#define NVIC_MAX_ALLOWED_IRQS 240UL
#endif

#ifdef CONFIG_ARCH_ARM_ARMV7M
#define NVIC_MAX_ALLOWED_IRQS 480UL
#endif

/**
 * Each SoC has its own NVIC configuration depending on its IP list
 */

#define NUM_IRQS __NVIC_VECTOR_LEN

/* arch specific API */
/*@
  assigns ((SCB_Type*)SCB_BASE)->AIRCR;
 */
void     nvic_set_prioritygrouping(uint32_t PriorityGroup);

/* INFO: typo in CMSIS intrinsics.... fixed through asm-generic aliasing */
/*@
  assigns \nothing;
 */
uint32_t nvig_get_prioritygrouping(void);

/*@

  requires IRQn < NUM_IRQS;
  requires NUM_IRQS <= NVIC_MAX_ALLOWED_IRQS;

  behavior invalid_irq:
    assumes IRQn >= NUM_IRQS;
    assigns \nothing;
    ensures \result == K_ERROR_INVPARAM;

  behavior valid_irq:
    assumes IRQn < NUM_IRQS;
    assigns *NVIC;
    ensures \result == K_STATUS_OKAY;

  complete behaviors;
  disjoint behaviors;
 */
kstatus_t     nvic_enableirq(uint32_t IRQn);

/*@

  requires IRQn < NUM_IRQS;
  requires NUM_IRQS <= NVIC_MAX_ALLOWED_IRQS;

  behavior invalid_irq:
    assumes IRQn >= NUM_IRQS;
    assigns \nothing;
    ensures \result == K_ERROR_INVPARAM;

  behavior valid_irq:
    assumes IRQn < NUM_IRQS;
    assigns *NVIC;
    ensures \result == K_STATUS_OKAY;

  complete behaviors;
  disjoint behaviors;
 */
kstatus_t     nvic_disableirq(uint32_t IRQn);

/*@

  requires IRQn < NUM_IRQS;
  requires NUM_IRQS <= NVIC_MAX_ALLOWED_IRQS;
  assigns \nothing;

  behavior invalid_irq:
    assumes IRQn >= NUM_IRQS;
    ensures \result == 0;

  behavior valid_irq:
    assumes IRQn < NUM_IRQS;
    ensures \result == 0 || \result == 1;

  complete behaviors;
  disjoint behaviors;
 */
uint32_t    nvic_get_pendingirq(uint32_t IRQn);

/*@

  requires IRQn < NUM_IRQS;
  requires NUM_IRQS <= NVIC_MAX_ALLOWED_IRQS;

  behavior invalid_irq:
    assumes IRQn >= NUM_IRQS;
    assigns \nothing;
    ensures \result == K_ERROR_INVPARAM;

  behavior valid_irq:
    assumes IRQn < NUM_IRQS;
    assigns *NVIC;
    ensures \result == K_STATUS_OKAY;

  complete behaviors;
  disjoint behaviors;
 */
kstatus_t     nvic_set_pendingirq(uint32_t IRQn);

/*@

  requires IRQn < NUM_IRQS;
  requires NUM_IRQS <= NVIC_MAX_ALLOWED_IRQS;

  behavior invalid_irq:
    assumes IRQn >= NUM_IRQS;
    assigns \nothing;
    ensures \result == K_ERROR_INVPARAM;

  behavior valid_irq:
    assumes IRQn < NUM_IRQS;
    assigns *NVIC;
    ensures \result == K_STATUS_OKAY;

  complete behaviors;
  disjoint behaviors;
 */
kstatus_t     nvic_clear_pendingirq(uint32_t IRQn);

/*@
  requires IRQn < NUM_IRQS;
  requires NUM_IRQS <= NVIC_MAX_ALLOWED_IRQS;
  assigns \nothing;
 */
uint32_t nvic_get_active(uint32_t IRQn);


void     nvic_systemreset(void);


/* arch-generic naming definition, aliased to above (see nvic.c) */
kstatus_t     interrupt_enable_irq(uint32_t IRQn);
kstatus_t     interrupt_disable_irq(uint32_t IRQn);
uint32_t      interrupt_get_pending_irq(uint32_t IRQn);
kstatus_t     interrupt_set_pending_irq(uint32_t IRQn);
kstatus_t     interrupt_clear_pendingirq(uint32_t IRQn);

/* arch-genric API */
/*@
  assigns \nothing;
 */
inline __attribute__((always_inline)) void wait_for_interrupt(void) {
#ifndef __FRAMAC__
    arch_data_sync_barrier();
    arch_inst_sync_barrier();
    asm volatile ("wfi\r\n" : : : "memory");
#endif
}

/*@
  assigns \nothing;
 */
inline __attribute__((always_inline)) void wait_for_event(void) {
#ifndef __FRAMAC__
    arch_data_sync_barrier();
    arch_inst_sync_barrier();
    asm volatile ("wfe\r\n" : : : "memory");
#endif
}

/*@
  assigns \nothing;
 */
inline __attribute__((always_inline)) void notify_event(void) {
#ifndef __FRAMAC__
    arch_data_sync_barrier();
    arch_inst_sync_barrier();
    asm volatile ("sev\r\n" : : : "memory");
#endif
}

/*@
  assigns \nothing;
 */
static inline void interrupt_disable(void) {
#ifndef __FRAMAC__
    asm inline (
        "cpsid i\r\n"
            :::
            );
#endif
    return;
}

/*@
  assigns \nothing;
 */
static inline void interrupt_enable(void) {
#ifndef __FRAMAC__
    asm inline (
        "cpsie i\r\n"
            :::
    );
    arch_data_sync_barrier();
    arch_inst_sync_barrier();
#endif
    return;
}

/*@
  requires __NVIC_VECTOR_LEN <= NVIC_MAX_ALLOWED_IRQS;
  assigns *NVIC;
 */
static inline void interrupt_init(void) {
    for (size_t i = 0UL; i < NUM_IRQS; ++i) {
        nvic_disableirq(i);
        nvic_clear_pendingirq(i);
    }

    return;
}

/*@
  assigns ((SCB_Type*)SCB_BASE)->AIRCR;
 */
static inline void system_reset(void) {
    NVIC_SystemReset();
}

#endif/*NVIC_H*/
