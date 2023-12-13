// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-cortex-m/soc.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/arch/asm-cortex-m/systick.h>
#include <sentry/arch/asm-cortex-m/debug.h>
#include <sentry/arch/asm-cortex-m/handler.h>
#include <sentry/arch/asm-generic/platform.h>
#include <sentry/managers/memory.h>
#include <sentry/managers/interrupt.h>
#include <sentry/managers/debug.h>
#include <sentry/sched.h>
#include <sentry/io.h>

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

/**
 * Used subhandlers if the Rust submodule was built
*/
stack_frame_t *svc_handler_rs(stack_frame_t *frame);

void dump_frame(stack_frame_t *frame)
{
#ifndef CONFIG_BUILD_TARGET_RELEASE
    uint32_t msp, psp;
    pr_debug("== frame info");
    pr_debug("r0\t\t%08x\t\t%08d", frame->r0, frame->r0);
    pr_debug("r1\t\t%08x\t\t%08d", frame->r1, frame->r1);
    pr_debug("r2\t\t%08x\t\t%08d", frame->r2, frame->r2);
    pr_debug("r3\t\t%08x\t\t%08d", frame->r3, frame->r3);
    pr_debug("r4\t\t%08x\t\t%08d", frame->r4, frame->r4);
    pr_debug("r5\t\t%08x\t\t%08d", frame->r5, frame->r5);
    pr_debug("r6\t\t%08x\t\t%08d", frame->r6, frame->r6);
    pr_debug("r7\t\t%08x\t\t%08d", frame->r7, frame->r7);
    pr_debug("r8\t\t%08x\t\t%08d", frame->r8, frame->r8);
    pr_debug("r9\t\t%08x\t\t%08d", frame->r9, frame->r9);
    pr_debug("r10\t\t%08x\t\t%08d", frame->r10, frame->r10);
    pr_debug("r11\t\t%08x\t\t%08d", frame->r11, frame->r11);
    pr_debug("r12\t\t%08x\t\t%08d", frame->r12, frame->r12);
    pr_debug("lr\t\t%08x\t\t%08d", frame->lr, frame->lr);
    pr_debug("pc\t\t%08x\t\t%08d", frame->pc, frame->pc);
    pr_debug("prev_lr\t%08x\t\t%08d", frame->prev_lr, frame->prev_lr);
    pr_debug("xpsr\t%08x\t\t%08d", frame->xpsr, frame->xpsr);
    asm volatile (
        "mrs %0, msp\r\n"   /* r0 <- MSP */
        "mrs %1, psp\r\n"   /* or r0 <- PSP (process stack) */
    : "=r" (msp), "=r" (psp) ::);
    pr_debug("msp\t\t%08x\t\t%08d", msp, msp);
    pr_debug("psp\t\t%08x\t\t%08d", psp, psp);
#endif
}

__STATIC_FORCEINLINE secure_bool_t is_userspace_fault(stack_frame_t *frame) {
    secure_bool_t res = SECURE_FALSE;
    if (likely(frame->lr & 0x4UL)) {
        res = SECURE_TRUE;
    }
    return res;
}

__STATIC_FORCEINLINE stack_frame_t *may_panic(stack_frame_t *frame) {
    stack_frame_t *newframe = frame;
    if (is_userspace_fault(frame) == SECURE_TRUE) {
        taskh_t tsk = sched_get_current();
        /* user mode, fault source is userspace:
         *  1. set task as faulted
         *  2. elect another task
         */
        pr_debug("[%d] Userspace Oops!", handle_convert_taskh_to_u32(tsk));
        mgr_task_set_state(tsk, JOB_STATE_FAULT);
        tsk = sched_elect();
        mgr_task_get_sp(tsk, &newframe);
    } else {
        __do_panic();
        __builtin_unreachable();
    }
    return newframe;
}

/*
 * Replaced by real sentry _entrypoint at link time
 */
extern  __attribute__((noreturn)) void _entrypoint();

__STATIC_FORCEINLINE __attribute__((noreturn)) void hardfault_handler(stack_frame_t *frame)
{
    pr_debug("Hardfault!!!");
    if ((SCB->HFSR) & SCB_HFSR_FORCED_Pos) {
        pr_debug("hardfault forced (escalation)");
    } else {
        pr_debug("direct hardfault, no escalation");
    }
    if ((SCB->HFSR) & SCB_HFSR_VECTTBL_Pos) {
        pr_debug("Bus fault during vector table read.");
    }
#if defined(CONFIG_BUILD_TARGET_DEBUG)
    #if 0
    /* XXX: To be implemented, helper associated to kernel map */
    mgr_debug_dump_stack(frame);
    #endif
#endif
    dump_frame(frame);
    __platform_clear_flags();
    request_data_membarrier();
    __do_panic();
}

__STATIC_FORCEINLINE stack_frame_t *usagefault_handler(stack_frame_t *frame)
{
    stack_frame_t *newframe = frame;
    size_t cfsr = SCB->CFSR;
    pr_debug("Usagefault!!!");
    if (cfsr & SCB_CFSR_UNDEFINSTR_Msk) {
        pr_debug("Undefined instruction!");
    }
    if (cfsr & SCB_CFSR_INVSTATE_Msk) {
        pr_debug("invalid state!");
    }
    if (cfsr & SCB_CFSR_INVPC_Msk) {
        pr_debug("invalid PC!");
    }
    if (cfsr & SCB_CFSR_NOCP_Msk) {
        pr_debug("No coprocessor!");
    }
    if (cfsr & SCB_CFSR_UNALIGNED_Msk) {
        pr_debug("Unaligned memory access!");
    }
    if (cfsr & SCB_CFSR_DIVBYZERO_Msk) {
        pr_debug("Division by 0!");
    }
    dump_frame(frame);
    newframe = may_panic(frame);
    __platform_clear_flags();
    request_data_membarrier();
    return newframe;
}


__STATIC_FORCEINLINE stack_frame_t *memfault_handler(stack_frame_t *frame)
{
    stack_frame_t *newframe = frame;
    size_t cfsr = SCB->CFSR;
    pr_err("Memory fault !!!");
    if (cfsr & SCB_CFSR_IACCVIOL_Msk) {
        pr_debug("Instruction access violation!");
    }
    if (cfsr & SCB_CFSR_DACCVIOL_Msk) {
        pr_debug("Data access violation!");
    }
    if (cfsr & SCB_CFSR_MUNSTKERR_Msk) {
        pr_debug("Fault while unstacking from exception!");
    }
    if (cfsr & SCB_CFSR_MSTKERR_Msk) {
        pr_debug("Fault while stacking for exception entry!");
    }
    if (cfsr & SCB_CFSR_MMARVALID_Msk) {
        pr_debug("Fault at address %p", SCB->MMFAR);
    }
    dump_frame(frame);
    newframe = may_panic(frame);
    request_data_membarrier();
    return newframe;
}


__STATIC_FORCEINLINE stack_frame_t *svc_handler(stack_frame_t *frame)
{
    return svc_handler_rs(frame);
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
    stack_frame_t *newframe = frame;
    taskh_t current = sched_get_current();
    taskh_t next;

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
            /*@ assert \false; */
        case MEMMANAGE_IRQ:
            newframe = memfault_handler(frame);
            break;
        case USAGEFAULT_IRQ:
            newframe = usagefault_handler(frame);
            break;
        case SVC_IRQ:
            newframe = svc_handler(frame);
            break;
        case SYSTICK_IRQ:
            /* periodic, every each millisecond execution */
            newframe = systick_handler(frame);
            break;
        default:
            if (it >= 0) {
                newframe = userisr_handler(frame, it);
            }
            /* defaulting to nothing... */
            break;
    }

    /* the next job may not be the previous one */
    next = sched_get_current();
    if (unlikely(handle_convert_taskh_to_u32(current) != handle_convert_taskh_to_u32(next))) {
        /* context switching here, saving previous context (frame) to task
         * ctx before leaving.
         */
        if (unlikely(mgr_task_set_sp(current, (stack_frame_t*)__get_PSP()) != K_STATUS_OKAY)) {
             __do_panic();
        }
        /**
         * and then map next task memory
         * TODO: map next task ressources, demap previous one ressources too
         */
        if (unlikely(mgr_mm_map(MM_REGION_TASK_TXT, 0, next) != K_STATUS_OKAY)) {
            __do_panic();
        }
        if (unlikely(mgr_mm_map(MM_REGION_TASK_DATA, 0, next) != K_STATUS_OKAY)) {
            __do_panic();
        }
    } else {
        /* when no context switch happen (i.e. the same task is elected or no election),
           we may need to fallback to previous frame, as elect() may return an invalid frame
           (i.e. without the current saving). This is the case when the very same job is
           elected.
           when there is no election, this code as no effect (newframe == frame).
         */
        newframe = frame;
    }
    return newframe;
}


/**
 * @brief Reset handler, executed at POR time
 */
__attribute__((noreturn, used)) void Reset_Handler(void)
{
    uint32_t *src;
    uint32_t *p;
    uint32_t shcsr;
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

    /* enable supported fault handlers */
    shcsr = SCB_SHCSR_USGFAULTENA_Msk | SCB_SHCSR_MEMFAULTENA_Msk;
    iowrite32((size_t)&SCB->SHCSR, shcsr);
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
