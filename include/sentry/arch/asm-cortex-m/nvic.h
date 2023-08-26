// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef NVIC_H
#define NVIC_H

#include <arch/asm-cortex-m/membarriers.h>

inline __attribute__((always_inline)) void wait_for_interrupt(void) {
    arch_data_sync_barrier();
    arch_inst_sync_barrier();
    asm volatile ("wfi\r\n" : : : "memory");
}

inline __attribute__((always_inline)) void wait_for_event(void) {
    arch_data_sync_barrier();
    arch_inst_sync_barrier();
    asm volatile ("wfe\r\n" : : : "memory");
}

inline __attribute__((always_inline)) void notify_event(void) {
    arch_data_sync_barrier();
    arch_inst_sync_barrier();
    asm volatile ("sev\r\n" : : : "memory");
}

static inline void interrupt_disable(void) {
    asm inline (
        "cpsid i\r\n"
            :::
            );
    return;
}

static inline void interrupt_enable(void) {
    asm inline (
        "cpsie i\r\n"
            :::
    );
    arch_data_sync_barrier();
    arch_inst_sync_barrier();

    return;
}

static inline void interrupt_init(void) {
    for (size_t i = 0UL; i < CONFIG_NVIC_VECTORS; ++i) {
        nvic_disableirq(i);
        nvic_clear_pendingirq(i);
    }

    return;
}

void     nvic_set_prioritygrouping(uint32_t PriorityGroup);
uint32_t nvig_get_prioritygrouping(void);

void     nvic_enableirq(uint32_t IRQn);
void     nvic_disableirq(uint32_t IRQn);

uint32_t nvic_get_pendingirq(uint32_t IRQn);
void     nvic_set_pendingirq(uint32_t IRQn);

void     nvic_clear_pendingirq(uint32_t IRQn);
uint32_t nvic_get_active(uint32_t IRQn);
void     nvic_systemreset(void);


#endif/*NVIC_H*/
