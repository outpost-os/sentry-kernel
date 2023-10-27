// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-cortex-m/soc.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/arch/asm-cortex-m/systick.h>

/**
 * @file ARM Cortex-M generic handlers
 */

/* .bss informations generated in ldscript */
extern uint32_t _sbss;
extern uint32_t _ebss;
extern uint32_t _sidata;
extern uint32_t _sdata;
extern uint32_t _edata;

extern __irq_handler_t __vtor_table[];

/*
 * Replaced by real sentry _entrypoint at link time
 */
extern  __attribute__((noreturn)) void _entrypoint();

static __attribute__((noreturn)) void do_panic(void)
{
    /* XXX: here, a security policy should be considered. The do_panic() shoud call security manager
      primitive (potential cleanups) and other things to define */
    do {
        asm volatile("nop");
    } while (1);
}

static __attribute__((noreturn)) void hardfault_handler(stack_frame_t *frame)
{
#if defined(CONFIG_BUILD_TARGET_DEBUG)
    #if 0
    /* XXX: To be implemented, helper associated to kernel map */
    mgr_debug_dump_stack(frame);
    #endif
#if defined(CONFIG_WITH_JTAG_CONNECTED)
    /* explicit breakpoint in jtag mode (JTAG connected)*/
    asm volatile("bkpt");
#endif
#endif
    do_panic();
}


#define __GET_IPSR(intr) ({ \
    asm volatile ("mrs r1, ipsr\n\t" \
                  "mov %0, r1\n\t" \
                  : "=r" (intr) :: "r1" ); })


/**
 * @brief dispatcher and generic handler manager
 *
 * may not return the same frame pointer as received (through r0),
 * depending on the IRQ.
 *
 */
stack_frame_t *Default_SubHandler(stack_frame_t *frame)
{
    int it;
    /* get back interrupt name */
    __GET_IPSR(it);
    it &= IPSR_ISR_Msk;

    /*
     * As the vector received is unified for both core exception (negatives)
     * and NVIC interrupts (starting with 0), we need to decrement the vtor
     * value of 16 to realign.
     * This is required as the IRQ canonical name used by the NVIC start
     * at 0 for the first peripheral interrupt, which is, in term of
     * VTOR, the 16th one.
     */
    it-= 16;

    /* distatching here */
    switch (it) {
        case HARDFAULT_IRQ:
            /* calling hardfault handler */
            hardfault_handler(frame);
            break;
        case SYSTICK_IRQ:
            /* periodic, every each millisecond execution */
            frame = systick_handler(frame);
            break;
        default:
            /* defaulting to nothing... */
            break;
    }

    return frame;
}


/**
 * @brief Reset handler, executed at POR time
 */
__attribute__((noreturn, used)) void Reset_Handler(void)
{
    uint32_t *src;
    uint32_t *p;
    __disable_irq();

    /*
     * TODO:
     * Add a 'LOAD_FROM_ANYWHERE or something' config flag
     * In such a case, we can't make any assumption regarding
     * the current cpu state, so disable and clear any pending irq,
     * relocate vtor and set msp to the given value.
     */
#if 1
    for (uint32_t irqnum = 0; irqnum < __NVIC_VECTOR_LEN; irqnum++) {
        nvic_disableirq(irqnum);
        nvic_clear_pendingirq(irqnum);
    }

    systick_stop_and_clear();
#endif

    /* relocate vtor table */
    SCB->VTOR = (uint32_t)&__vtor_table[0];
    /* set main stack pointer to reset value */
    __set_MSP((uint32_t)__vtor_table[0]);

    /* enable FPU access if used */
#if defined (__FPU_USED) && (__FPU_USED == 1U)
    SCB->CPACR |= ((3U << 10U*2U) |     /* enable CP10 Full Access */
                   (3U << 11U*2U)  );   /* enable CP11 Full Access */
#endif

    /* clear bss */
    for (p = &_sbss; p < &_ebss; p++) {
        *p = 0UL;
    }

    /* data relocatation */
    /* XXX:
     *  /!\ We may relocate only data.rel.ro section /!\
     */
    for (src = &_sidata, p = &_sdata; p < &_edata; p++) {
        *p = *src++;
    }

    /* branch to sentry kernel entry point */
    _entrypoint();

    /* should never return */
    /*@ assert \false; */
}

__STATIC_FORCEINLINE void save_context(void)
{
    asm volatile (
    "cpsid   i\r\n"         /* Disable all interrupts */
    "tst     lr, #4\r\n"    /* bit 2: (0) MSP (1) PSP stack */
    "ite     eq\r\n"        /* if equal 0 */
    "mrseq   r0, msp\r\n"   /* r0 <- MSP */
    "mrsne   r0, psp\r\n"   /* or r0 <- PSP (process stack) */
    "stmfd   r0!, {r4-r11, lr}\r\n"
    "tst     lr, #4\r\n"    /* bit 2: (0) MSP (1) PSP stack */
    "ite     eq\r\n"        /* if equal 0 */
    "msreq   msp, r0\r\n"   /* MSP <- r0 */
    "msrne   psp, r0\r\n"   /* PSP <- r0 */
    );
}

__STATIC_FORCEINLINE void restore_context(void)
{
    asm volatile (
    "ldmfd   r0!, {r4-r11, lr}\r\n"
    "tst     lr, #4\r\n"    /* bit 2: (0) MSP (1) PSP stack      */
    "bne     100f\r\n"      /* if not equal 0, moving back to PSP context */
    "msr     msp, r0\r\n"   /* msp-use then: going back to MSP context */
    "isb\r\n"
    "cpsie   i\r\n"
    "bx      lr\r\n"
    "100:\r\n"
    "msr     psp, r0\r\n"   /* PSP <- r0 */
    "mov r0, #2\r\n"
    "cmp r1, #1\r\n"
    "adc r0, r0, #0\r\n"
    "msr     control, r0\r\n"
    "isb\r\n"
    "cpsie   i\r\n"
    "bx      lr\r\n");
}

/**
 * @brief Default handler for all others
 *
 * TODO: fix some of the asm that can be done with inline function instead, to
 * avoid redundancy. By now, some others handlers are missing, (hardfault, svc....)
 * that will require some generic handler entry/leave asm code
 */
__attribute__((naked)) __attribute__((used)) void Default_Handler(void)
{
    save_context();
    asm volatile (
        "bl Default_SubHandler"
    );
    restore_context();
}
