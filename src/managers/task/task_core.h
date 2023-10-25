// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef TASK_CORE_H
#define TASK_CORE_H

#include <sentry/managers/task.h>

typedef struct task {
    const task_meta_t *metadata; /**< task metadata (const, build-time, informations) */
    /*
     * Task context information, these fields store dynamic values, such as current
     * task frame, current received ipc or signal events from others, etc.
     * Only fully sched-relative infos (current quantum) are not stored in the task
     * structure but directly in the scheduler context, when the scheduler do support
     * such model (quantum-based).
     */
    thread_state_t  state;      /**< current task state */
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
                                        source identifier */
} task_t;

/**
 * @file task core functions private API for task manager internal
 */

task_t *task_get_table(void);

#endif/*!TASK_INIT_H*/
