// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef TASK_H
#define TASK_H

#include <sentry/device.h>
#include <sentry/dma.h>
#include <sentry/ipc.h>
#include <sentry/signal.h>

#include <assert.h>
#include <inttypes.h>
#include <stddef.h>

/**
 * \file sentry kernel generic types
 */

#ifndef CONFIG_MAX_DEV_PER_TASK
#define CONFIG_MAX_DEV_PER_TASK 8U
#endif

#ifndef CONFIG_MAX_SHM_PER_TASK
#define CONFIG_MAX_SHM_PER_TASK 8U
#endif

/**
 * To be fixed... not ordonned. Basic placement of stack-based register saving
 * (NVIC auto-saving + complement by runtime or kernel)
 */
typedef struct task_frame {
    uint32_t    r4;
    uint32_t    r5;
    uint32_t    r6;
    uint32_t    r7;
    uint32_t    r8;
    uint32_t    r9;
    uint32_t    r10;
    uint32_t    r11;
    uint32_t    exc_return;
    uint32_t    r3;
    uint32_t    r2;
    uint32_t    r1;
    uint32_t    r0;
    uint32_t    r12;
    uint32_t    lr;
    uint32_t    pc;
    uint32_t    psr;
} task_frame_t;

static_assert(sizeof(task_frame_t) == (17*sizeof(uint32_t)), "Invalid stack frame size");

/** Basic signals that are handled at UAPI level. If more
  complex signal handling is required, IPC with upper layer protocol
  is needed.
  These signal can be used in order to avoid any memory copy, only scheduling
  the peer. The kernel guarantee that the signal is transmitted to the peer, but
  not that the peer do check for it (it is under the peer implementation responsability
  to handle a single blocking point with an input event blocking method that wait for,
  at least, signals).
  In IoT condition, these signals can be used for multiple usage while they keep the
  initial POSIX scementic.
  The standard POSIX USR1 and 2 signals are also defined to allow tasks to communicate
  through these two signals for custom events
  The userspace POSIX implementation of signals can be based on the sentry signal support,
  to avoid IPC-based data transmission for most signal events. INFO: by now, no spawned sighandler
  is supported, instead, a wait_for_event() call can be made in the main thread. Spawning
  threads is complex and do consume a lot of memory.
*/
typedef enum signal {
    SIGNAL_ABORT,   /**< Abort signal */
    SIGNAL_ALARM,   /**< timer (from alarm) */
    SIGNAL_BUS,     /**< bus error (bad memory access, memory required)*/
    SIGNAL_CONT,    /**< continue if previously stopped */
    SIGNAL_ILL,     /**< illegal instruction. Can be also used for upper protocols */
    SIGNAL_IO,      /**< I/O now ready */
    SIGNAL_PIPE,    /**< broken pipe */
    SIGNAL_POLL,    /**< event pollable */
    SIGNAL_TERM,    /**< termination signal. Can be used to stop an IPC stream for e.g. (remote process termination is not possible) */
    SIGNAL_TRAP,    /**< trace/bp signal (debug usage )*/
    SIGNAL_USR1,    /**< 1st user-defined signal */
    SIGNAL_USR2,    /**< 2nd user-defined signal */
} signal_t;

typedef enum thread_state {
      THREAD_STATE_NOTSTARTED, /**< thread has not started yet. For not automatically started tasks */
      THREAD_STATE_READY,     /**< thread ready, wait for being scheduled */
      THREAD_STATE_SLEEPING, /**< sleeping, can be awoken by any ISR (wfi()-like) */
      THREAD_STATE_SLEEPING_DEEP, /**< deep sleep, IRQ deactivated for the given sleep time */
      THREAD_STATE_FAULT,     /**< userspace fault event, not schedulable */
      THREAD_STATE_SECURITY,  /**< security event risen, not schedulable */
      THREAD_STATE_FINISHED,  /**< thread terminated, returned from thread entrypoint */
      THREAD_STATE_IPC_SEND_BLOCKED, /**< emitted an IPC, wait for receiver to process */
      THREAD_STATE_IPC_SIG_RECV_BLOCKED, /**< listening on IPC&signals events but no event received by now */
} thread_state_t;


typedef struct task {
    size_t          s_text;           /**< start address of .text section */
    size_t          text_size;        /**< text section size */
    size_t          s_rodata;         /**< start address of .data section */
    size_t          rodata_size;      /**< text section size */
    size_t          s_data;           /**< start address of .data section */
    size_t          data_size;        /**< text section size */
    uint16_t        main_offset;      /**< offset of main() in text section */
    size_t          stack_top;        /**< main thread stack top address */
    uint16_t        stack_size;       /**< main thtrad stack size */

    size_t          isr_stack_top;    /**< ISR handler stack top address (used at spawn time)*/
    uint16_t        isr_stack_size;   /**< ISR handler stack size (should be small)*/

    size_t          heap_base;        /**< process heap base. Always set */
    uint16_t        heap_size;        /**< process heap size. Can be 0 (no heap)*/

    uint8_t         num_shm;          /**< number of shared memories */
    uint8_t           shared_memory[CONFIG_MAX_SHM_PER_TASK];/**< SHM metadatas */ /* shm_t to define*/
    uint8_t         num_devs;         /**< number of devices */
    device_t        devices[CONFIG_MAX_DEV_PER_TASK]; /**< devices metadata */
#if CONFIG_DMA_SUPPORT
    uint8_t         num_dmas;         /**< number of DMA streams */
    dma_t           dmas[CONFIG_MAX_DMA_STREAMS_PER_TASK]; /**< DMA streams metadata */
#endif

#if CONFIG_DOMAIN
    uint8_t         domain;           /**< domain identifier. Depending on the configured domain
                                            policy, process ability to communicate with others,
                                            process scheduling policy and process election
                                            pre- and post- phases may be affected.
                                             */
#endif

    /* about state, priority and quantum consumtion */
    thread_state_t  state;         /**< current task state */
    uint8_t         priority;      /**< task priority */
    uint8_t         base_quantum;  /**< task configured quantum */
    uint8_t         current_quantum;   /**< task current quantum value */

    /* about contexts */
    task_frame_t    ctx;  /**< current process lonely thread stack context */
    /* about events */
    ipc_context_t   ipc_events; /**<
                                Each task only has one IPC context (only blocking IPC supported).
                                When sending IPC, the thread is deschedule and wait for the other
                                to read for its IPC content (no double user/kernel copy, only
                                user-to-user blob) ensured by disabled reentrancy in kernel.
                                The context hold only, for a given task, the info indicating if
                                there is an IPC received and its effective size.
                                When impacting the thread state (blocking IPC, the state falg
                                is used)
                                */
    signal_context_t signal_events; /**< incomming signal if received, storing signal type and
                                        source identifier
                                        */
} task_t;

void initialize_stack_context(size_t sp, size_t pc);

#endif/*TASK_H*/
