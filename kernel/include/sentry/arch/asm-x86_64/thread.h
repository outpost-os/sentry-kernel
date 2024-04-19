// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __THREAD_H
#define __THREAD_H

/**
 * \file context manipulation, including kernel threads
 */
#include <inttypes.h>
#include <stddef.h>

#ifdef TEST_MODE
/* local basic definitions for test mode */
#define EXC_RETURN_THREAD_PSP 0xfffffff1
#define EXC_RETURN_THREAD_MSP 0xfffffff9
#endif

#ifndef __FRAMAC__
/* x86_64 typical stack frame */
typedef struct stack_frame {
    /**< backed by default handler */

    uint64_t rax, rbx, rcx, rdx, rsi, rdi, rbp, rsp;
    /**< backed automatically by NVIC */
    uint64_t r8, r9, r10, r11, r12, r13, r14, r15, rip;
    uint16_t cs, ss, ds, es, fs, gs;
} __attribute__((packed)) stack_frame_t;

static inline stack_frame_t *__thread_init_stack_context(uint32_t rerun, size_t sp, size_t pc, size_t got)
{
    stack_frame_t*  frame = (stack_frame_t*)(sp - sizeof(stack_frame_t));
    frame->rax = rerun;
    frame->rbx = 0x0; /* seed to 0 on x86_64 */
    frame->rcx = 0x0;
    frame->rdx = 0x0;
    frame->rsi = 0x0;
    frame->rdi = 0x0;
    frame->rbp = 0x0;
    frame->rsp = 0x0;
    frame->r8 = 0x0;
    frame->r9 = got;
    frame->r10 = 0x0;
    frame->r11 = 0x0;
    frame->r12 = 0x0;
    frame->r13 = 0x0;
    frame->r14 = 0x0;
    frame->r15 = 0x0;
    frame->rip = pc;
    frame->cs = 0x0;
    frame->ss = 0x0;
    frame->ds = 0x0;
    frame->es = 0x0;
    frame->fs = 0x0;
    frame->gs = 0x0;
    return frame;
}
#endif

#endif/*__THREAD_H*/
