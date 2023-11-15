// SPDX-FileCopyrightText: 2023 Ledge SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __PLATFORM_H_
#define __PLATFORM_H_

#ifndef PLATFORM_H
#error "arch specific header must not be included directly!"
#endif

#include <sentry/arch/asm-cortex-m/system.h>
#include <sentry/arch/asm-cortex-m/scb.h>
#include <sentry/arch/asm-cortex-m/thread.h>
#include <sentry/io.h>

#define THREAD_MODE_USER    0xab2f5332UL
#define THREAD_MODE_KERNEL  0x5371a247UL

/**
 * @def alignment size of sections. 4bytes on ARM32
 */
#define SECTION_ALIGNMENT_LEN 0x4UL


static inline void __attribute__((noreturn)) __platform_spawn_thread(size_t entrypoint, stack_frame_t *stack_pointer, uint32_t flag) {
  /*
   * Initial context switches to main core thread (idle_thread).
   */
  uint32_t runlevel;
  runlevel = 3;  /* user, PSP */
  if (flag == THREAD_MODE_KERNEL) {
    runlevel = 2; /* privileged, PSP */
  }
	asm volatile
       ("mov r0, %[SP]      \n\t"   \
        "msr psp, r0        \n\t"   \
        "mov r0, %[LVL]     \n\t"   \
        "msr control, r0    \n\t"   \
	      "mov r1, %[PC]      \n\t"   \
	      "bx r1              \n\t"   \
        :
        : [PC] "r" (entrypoint),
          [SP] "r" (stack_pointer),
          [LVL] "r" (runlevel)
        : "r0", "r1");
        __builtin_unreachable();
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
