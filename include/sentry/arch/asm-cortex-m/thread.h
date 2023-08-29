// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __THREAD_H_
#define __TRHEAD_H_
/**
 * \file context manipulation, including kernel threads
 */

/* type of return mode (return to MSP, return to PSP, or return to interrupt) */
#define EXC_THREAD_MODE    0xFFFFFFFD
#define EXC_MSP_MODE       0xFFFFFFF9
#define EXC_HANDLER_MODE   0xFFFFFFF1

/* the firmware bare default handler save the overall missing registers (i.e.
 * not saved by the NVIC) on the stack, generating a stack frame with a full
 * registers backup (see startup.s file).
 * This frame has the following structure:
 */
typedef struct stack_frame {
    /**< backed by default handler */
    uint32_t r4, r5, r6, r7, r8, r9, r10, r11, lr;
    /**< backed automatically by NVIC */
    uint32_t r0, r1, r2, r3, r12, prev_lr, pc, xpsr;
} __attribute__((packed)) stack_frame_t;

static inline void __thread_init_stack_context(uint32_t *sp, uint32_t pc)
{
    stack_frame_t*  frame = (stack_frame_t*)((uint32_t)sp - sizeof(stack_frame_t));
    frame->r0 = 0x0;
    frame->r1 = 0x0;
    frame->r2 = 0x0;
    frame->r3 = 0x0;
    frame->r4 = 0x0;
    frame->r4 = 0x0;
    frame->r5 = 0x0;
    frame->r6 = 0x0;
    frame->r7 = 0x0;
    frame->r8 = 0x0;
    frame->r9 = 0x0;
    frame->r10 = 0x0;
    frame->r11 = 0x0;
    frame->r12 = 0x0;
    frame->pc = (pc | 0x1); /* thumb2 mode */
    frame->lr = EXC_THREAD_MODE;
    return;
}

#endif/*__THREAD_H_*/
