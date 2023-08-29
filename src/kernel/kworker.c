// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <arch/asm-generic/interrupt.h>

/*
 * address if the PSP idle stack, as defined in the layout (see sentry.ld)
 */
extern uint32_t _idlestack;
static uint32_t* idle_stack_pointer = (uint32_t*)&_idlestack;

/*
 * address if the PSP kworker stack, as defined in the layout (see sentry.ld)
 */
extern uint32_t _kworkerstack;
static uint32_t* kworker_stack_pointer = (uint32_t*)&_kworkerstack;


/**
 * \file Kernel worker thread that manipulate kernel input queues
 */


/**
 * Idle thread, when there is just nothing to do....
 */
static void idle_thread(void)
{
    /* cpsid e is required in order to be able to wait, in a future implementation,
     * a tickless wait should be implemented to avoid it-based wait */
    do {
        wait_for_event();
    } while (1);
}


/**
 * Kworker thread, that handle async kernel events (sleep mode timeout, etc...)
 * Execute loads that can't be kept in handler mode with interrupts disabled for
 * too long, as kworker is preemptible
 */
static void kworker_thread(void)
{
    /*
     * at init time, kworker create the idle thread and all userspace tasks
     * threads, and initialize the scheduling.
     * Then it loops on its incomming queue, and yield if there is nothing to do,
     * leaving the thread election (including the kworker thread) under the
     * scheduler policy responsability
     */
}
