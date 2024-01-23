// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef NVIC_H
#define NVIC_H

#include <stddef.h>
#include <sentry/arch/asm-cortex-m/membarriers.h>
#include "soc.h"

/**
 * Each SoC has its own NVIC configuration depending on its IP list
 */


/* arch specific API */
void     nvic_set_prioritygrouping(uint32_t PriorityGroup);
/* INFO: typo in CMSIS intrinsics.... fixed through asm-generic aliasing */
uint32_t nvig_get_prioritygrouping(void);

void     nvic_enableirq(uint32_t IRQn);
void     nvic_disableirq(uint32_t IRQn);

uint32_t nvic_get_pendingirq(uint32_t IRQn);
void     nvic_set_pendingirq(uint32_t IRQn);

void     nvic_clear_pendingirq(uint32_t IRQn);
uint32_t nvic_get_active(uint32_t IRQn);
void     nvic_systemreset(void);


/* arch-generic naming definition, aliased to above (see nvic.c) */
void     interrupt_enable_irq(uint32_t IRQn);
void     interrupt_disable_irq(uint32_t IRQn);
uint32_t interrupt_get_pending_irq(uint32_t IRQn);
void     interrupt_set_pending_irq(uint32_t IRQn);

/* arch-genric API */
inline __attribute__((always_inline)) void wait_for_interrupt(void) {
#ifndef __FRAMAC__
    arch_data_sync_barrier();
    arch_inst_sync_barrier();
    asm volatile ("wfi\r\n" : : : "memory");
#endif
}

inline __attribute__((always_inline)) void wait_for_event(void) {
#ifndef __FRAMAC__
    arch_data_sync_barrier();
    arch_inst_sync_barrier();
    asm volatile ("wfe\r\n" : : : "memory");
#endif
}

inline __attribute__((always_inline)) void notify_event(void) {
#ifndef __FRAMAC__
    arch_data_sync_barrier();
    arch_inst_sync_barrier();
    asm volatile ("sev\r\n" : : : "memory");
#endif
}

static inline void interrupt_disable(void) {
#ifndef __FRAMAC__
    asm inline (
        "cpsid i\r\n"
            :::
            );
#endif
    return;
}

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

static inline void interrupt_init(void) {
    for (size_t i = 0UL; i < __NVIC_VECTOR_LEN; ++i) {
        nvic_disableirq(i);
        nvic_clear_pendingirq(i);
    }

    return;
}

static inline void system_reset(void) {
    NVIC_SystemReset();
}


#define NUM_IRQS __NVIC_VECTOR_LEN

#endif/*NVIC_H*/
