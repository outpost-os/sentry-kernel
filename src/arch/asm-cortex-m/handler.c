// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-cortex-m/irq_defs.h>

/**
 * @file ARM Cortex-M generic handlers
 */

/* .bss informations generated in ldscript */
extern uint32_t _sbss;
extern uint32_t _ebss;

/**
 * Replaced by real sentry _entrypoint at link time
 */
extern  __attribute__((weak)) void _entrypoint(){}
extern  __attribute__((weak)) void Default_SubHandler(){}

/**
 * @brief Reset handler, executed at POR time
 */
__attribute__((naked)) __attribute__((noreturn)) void Reset_Handler(void)
{
    interrupt_disable();
    /* Init VTOR and MSP stack address */
    asm volatile(
        "movs    r5, lr\r\n"
        "sub     r5, #5\r\n"  /* In thumb mode LR is pointing to PC + 4 bytes  + 1 because in thumb mode LR must be odd aligned*/
        "sub     r2, r5, %0\r\n" /* Compute vector table, based on generated table length (see input operand) */
        "ldr     r2, [r2]\r\n"
        "msr     msp, r2\r\n" /* store stack address fixed in vtor block in MSP */
        :
        : "i" (__NVIC_VECTOR_LEN*sizeof(void*))
        :
    );
    /* voluntary no .data copy. There must not have .data in a kernel */
    /* zeroify .bss, basic model, no builtins, highly optimisable by compiler */
    for (uint32_t *ptr = &_sbss; ptr < &_ebss; ++ptr) {
        *ptr = 0x0UL;
    }
    arch_data_sync_barrier();
    /* call entrypoint now */
    _entrypoint();
    /* should never return */
    /*@ assert \false; */
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
    asm volatile (
    "cpsid i\r\n"           /* Disable all interrupts */
    "tst     lr, #4\r\n"    /* bit 2: (0) MSP (1) PSP stack */
    "ite     eq\r\n"        /* if equal 0 */
    "mrseq   r0, msp\r\n"   /* r0 <- MSP */
    "mrsne   r0, psp\r\n"   /* or r0 <- PSP (process stack) */
    "stmfd   r0!, {r4-r11, lr}\r\n"
    "tst     lr, #4\r\n"    /* bit 2: (0) MSP (1) PSP stack */
    "ite     eq\r\n"        /* if equal 0 */
    "msreq   msp, r0\r\n"   /* MSP <- r0 */
    "msrne   psp, r0\r\n"   /* PSP <- r0 */
    "bl Default_SubHandler\r\n"
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
