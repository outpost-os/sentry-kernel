// SPDX-FileCopyrightText: 2023 Ledge SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __PLATFORM_H_
#define __PLATFORM_H_

#ifndef PLATFORM_H
#error "arch specific header must not be included directly!"
#endif

#include <sentry/arch/asm-cortex-m/system.h>
#include <sentry/arch/asm-cortex-m/scb.h>
#include <sentry/arch/asm-cortex-m/platform.h>
#include <sentry/io.h>
#include <sentry/thread.h>


static inline void __platform_spawn_kthread(kthread_t kernel_thread, size_t kthread_stack_pointer) {
    /*
     * Initial context switches to main core thread (idle_thread).
     */
	asm volatile
       ("mov r0, %[SP]      \n\t"   \
        "msr psp, r0        \n\t"   \
        "mov r0, 2          \n\t"   \
        "msr control, r0    \n\t"   \
	      "mov r1, %[PC]      \n\t"   \
	      "bx r1              \n\t"   \
        :
        : [PC] "r" (kernel_thread),
          [SP] "r" (kthread_stack_pointer)
        : "r0", "r1");
        return;
}

static inline void __platform_clear_flags(void) {
    /*
     * clean potential previous faults, typically when using jtag flashing
     */
    uint32_t cfsr = ioread32((size_t)r_CORTEX_M_SCB_CFSR);
    iowrite32((size_t)r_CORTEX_M_SCB_CFSR, cfsr | cfsr);
    return;
}


void __platform_init(void);


#endif/*!__PLATFORM_H_*/
