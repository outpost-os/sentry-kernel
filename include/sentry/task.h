// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef TASK_H
#define TASK_H

#include <assert.h>
#include <inttypes.h>
#include <stddef.h>

#include <uapi/handle.h>
#include <sentry/device.h>
#include <sentry/dma.h>
#include <sentry/ipc.h>
#include <sentry/signal.h>

/**
 * \file sentry kernel generic types
 */

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/thread.h>
#elif defined(__x86_64__)
#include <sentry/arch/asm-x86_64/thread.h>
#elif defined(__i386__)
#include <sentry/arch/asm-i386/thread.h>
#else
#error "unsupported architecture!"
#endif


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
      THREAD_STATE_ABORTING,  /**< on fault, handling abort-equivalent libc garbage collect. if the task
                                 implement a sigabrt() handler, the garbage collector execute the user-defined
                                 function before leaving */
      THREAD_STATE_FINISHED,  /**< thread terminated, returned from thread entrypoint */
      THREAD_STATE_IPC_SEND_BLOCKED, /**< emitted an IPC, wait for receiver to process */
      THREAD_STATE_IPC_SIG_RECV_BLOCKED, /**< listening on IPC&signals events but no event received by now */
} thread_state_t;


/**
 * This is the main task structure manipulated by the kernel. Each task build (ELF generation)
 * produce a blob that contain such binary format.
 * The structure is generated using as input:
 * - the ELF metadatas
 * - the task informations (permissions, configuration, dts information, etc.)
 * - the task label (16 bits unique identifier, like, for e.g. 0xbabe or 0x1051)
 *
 * when generated, the task structure is stored as a standalone file in the build system
 * so that it can be easily dumped by python tooling, and also pushed into the kernel image
 * in a dedicated task list section where all tasks info are stored.
 */
typedef struct task {
    /**
     * Task and struct identification part
     */
    uint64_t        magic;         /**< task structure magic number */
    uint32_t        version;       /**< structure version, may vary based on SDK version */
    taskh_t         id;            /**< task identifier (see handle.h, starting with rerun=0) */
    uint8_t         priority;      /**< task priority */
    uint8_t         quantum;       /**< task configured quantum */
    uint32_t        permissions;   /**< TBD(storage): task permission mask */

    /**
     * Memory mapping information, used for context switching and MPU configuration
     */
    size_t          s_text;           /**< start address of .text section */
    size_t          text_size;        /**< text section size */
    size_t          s_rodata;         /**< start address of .data section */
    size_t          rodata_size;      /**< text section size */
    size_t          s_data;           /**< start address of .data section */
    size_t          data_size;        /**< text section size */
    uint16_t        main_offset;      /**< offset of main() in text section */
    size_t          stack_top;        /**< main thread stack top address */
    uint16_t        stack_size;       /**< main thtrad stack size */

    size_t          heap_base;        /**< process heap base. Always set */
    uint16_t        heap_size;        /**< process heap size. Can be 0 (no heap)*/

    /**
     * Task ressources, that may also requires memory mapping, and associated perms
     */
    uint8_t         num_shm;          /**< number of shared memories */
    uint8_t         shared_memory[CONFIG_MAX_SHM_PER_TASK];/**< SHM metadatas */ /* shm_t to define*/
    uint8_t         num_devs;         /**< number of devices */
    device_t        devices[CONFIG_MAX_DEV_PER_TASK]; /**< devices metadata */
    uint8_t         num_dmas;         /**< number of DMA streams */
    uint8_t         dmas[CONFIG_MAX_DMA_STREAMS_PER_TASK]; /**< DMA streams metadata
                                        FIXME: define dma_t bitfield or struct */

    /**
     * domain management. Ignore if HAS_DOMAIN is not set
     */
    uint8_t         domain;           /**< domain identifier. Depending on the configured domain
                                            policy, process ability to communicate with others,
                                            process scheduling policy and process election
                                            pre- and post- phases may be affected.
                                             */

    /*
     * Task context information, these fields store dynamic values, such as current
     * task frame, current received ipc or signal events from others, etc.
     * Only fully sched-relative infos (current quantum) are not stored in the task
     * structure but directly in the scheduler context, when the scheduler do support
     * such model (quantum-based).
     */

    /* about contexts */
    thread_state_t   state;         /**< current task state */
    stack_frame_t   *sp;        /**< current process lonely thread stack context */
    /* about events */
    ipc_context_t   ipc_events; /**<
                                Each task only has one IPC context (only blocking IPC supported).
                                When sending IPC, the thread is preempted and wait for the other
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
    /*
     * Security part: the structure itself and the associated task memory
     * is checked using HMAC, based on a private key used at production time and
     * verified by the kernel at startup time
     */
    uint8_t         task_hmac[32]; /**< task .text+.rodata+.data build time hmac calculation (TBD)*/
    uint8_t         metadata_hmac[32]; /**< current struct build time hmac calculation */
} task_t;

void initialize_stack_context(size_t sp, size_t pc);

#endif/*TASK_H*/
