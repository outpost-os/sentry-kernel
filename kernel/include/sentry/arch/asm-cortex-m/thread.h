// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __THREAD_H_
#define __THREAD_H_
/**
 * \file context manipulation, including kernel threads
 */
#include <inttypes.h>
#include <stddef.h>
#include <assert.h>

#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/managers/security.h>

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

static_assert(sizeof(stack_frame_t) == (17*sizeof(uint32_t)), "Invalid stack frame size");


static inline stack_frame_t *__thread_init_stack_context(uint32_t rerun, size_t sp, size_t pc)
{
    /* on ARM, 4 first arguments are passed using registers R0 -> r3 */
    uint32_t seed = 0;
    if (unlikely(mgr_security_entropy_generate(&seed) != K_STATUS_OKAY)) {
        return NULL;
    }
    stack_frame_t*  frame = (stack_frame_t*)(sp - sizeof(stack_frame_t));
    frame->r0 = rerun;
    frame->r1 = seed;
    frame->r2 = 0x0;
    frame->r3 = 0x0;
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
    frame->xpsr = 0x21000200UL;
#if defined(CONFIG_FPU_HARDFP_ABI)
    frame->lr = EXC_RETURN_THREAD_PSP_FPU;
    frame->prev_lr = EXC_RETURN_THREAD_PSP_FPU; /* _start LR */
#else
    frame->lr = EXC_RETURN_THREAD_PSP;
    frame->prev_lr = EXC_RETURN_THREAD_PSP; /* _start LR */
#endif
    return frame;
}

#endif/*__THREAD_H_*/
