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
#include <sentry/managers/security.h>
#include <sentry/io.h>

#define THREAD_MODE_USER    0xab2f5332UL
#define THREAD_MODE_KERNEL  0x5371a247UL


#ifndef __WORDSIZE
#define __WORDSIZE 4UL
#endif

/**
 * @def alignment size of sections. 4bytes on ARM32
 */
#define SECTION_ALIGNMENT_LEN 0x4UL

static inline uint32_t __platform_get_current_sp(void) {
  uint32_t sp;
  asm volatile(
    "mov %0, sp"
    : "=r" (sp)
    :
    :);
    return sp;
}

/**
 * @def refuses unaligned accesses (word unaligned access for
 * word accesses or hword unaligned for hword accesses)
 * unaligned accesses is a path to multiple bugs such as invalid
 * htons/ntohs, invalid remote communication for hosts with strict
 * alignment, performances impacts, cache impact, etc.
 *
 * when activated, unaligned access generates UsageFault
 */
static inline void __platform_enforce_alignment(void) {
    SCB->CCR |= SCB_CCR_UNALIGN_TRP_Msk;
    request_data_membarrier();
}

static inline void __attribute__((noreturn)) __platform_spawn_thread(size_t entrypoint, stack_frame_t *stack_pointer, uint32_t flag) {
  /*
   * Initial context switches to main core thread (idle_thread).
   */
  uint32_t runlevel = 0; /* spawning very first thread here, rerun == 0*/
  uint32_t seed = 0UL;
  /* at init time, used for idle task only, RNG is setup, should not fail */
  mgr_security_entropy_generate(&seed);
  runlevel = 3;  /* user, PSP */
  if (flag == THREAD_MODE_KERNEL) {
    runlevel = 2; /* privileged, PSP */
  }
	asm volatile
       ("mov r0, %[SP]      \n\t"   \
        "msr psp, r0        \n\t"   \
        "mov r0, %[LVL]     \n\t"   \
        "msr control, r0    \n\t"   \
        "mov r0, %[THREADID] \n\t"   \
        "mov r1, %[SEED]    \n\t"   \
	      "mov r5, %[PC]      \n\t"   \
	      "bx r5              \n\t"   \
        :
        : [PC] "r" (entrypoint),
          [SP] "r" (stack_pointer),
          [LVL] "r" (runlevel),
          [THREADID] "r" (runlevel),
          [SEED] "r" (seed)
        : "r0", "r1", "r5");
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

static inline void __attribute__((noreturn)) __platform_start_userspace(void)
{
    //pr_debug("spawning thread, pc=%p, sp=%p", pc, sp);
    size_t icsr;
    //__platform_spawn_thread(pc, sp, THREAD_MODE_USER);
    /* force Pendsv interrupt to initiate first schedule */
    icsr = ioread32(SCB->ICSR);
    icsr |= SCB_ICSR_PENDSVSET_Msk;
    iowrite32((size_t)&SCB->ICSR, icsr);
    __ISB();
    __DSB();
    do { asm volatile ("nop"); } while (1);
    __builtin_unreachable();
}

void __platform_init(void);


#endif/*!__PLATFORM_H_*/
