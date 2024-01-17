// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef TASK_CORE_H
#define TASK_CORE_H

#include <sentry/managers/task.h>
#include <sentry/arch/asm-generic/memory.h>

#define TASK_EVENT_QUEUE_DEPTH 16

/* this structure is 32bits multiple ensured */
typedef struct __attribute__((packed)) task_event {
    uint32_t events[TASK_EVENT_QUEUE_DEPTH]; /** all event (inth_t, sigh_t and ipch_t) are uint32_t */
    uint8_t size;
    uint8_t num_ev;
    uint8_t _start;
    uint8_t _end;
} task_event_t;

/**
 * @brief enqueuing event into one of the task input queues
 */
static inline kstatus_t task_enqueue_event(uint32_t ev, task_event_t *queue) {
    kstatus_t status;
    if (unlikely(queue->num_ev == TASK_EVENT_QUEUE_DEPTH)) {
        status = K_ERROR_BUSY;
        goto err;
    }
    queue->events[queue->_end] = ev;
    queue->_start = (queue->_end + 1) % TASK_EVENT_QUEUE_DEPTH;
    queue->num_ev++;
    status = K_STATUS_OKAY;
err:
    return status;
}

/**
 * @brief dequeuing event from one of the task input queues
 */
static inline kstatus_t task_dequeue_event(uint32_t *ev, task_event_t *queue) {
    kstatus_t status;
    if (unlikely(queue->num_ev == 0)) {
        status = K_ERROR_NOENT;
        goto err;
    }
    *ev = queue->events[queue->_start];
    queue->_start = (queue->_start + 1) % TASK_EVENT_QUEUE_DEPTH;
    queue->num_ev--;
    status = K_STATUS_OKAY;
err:
    return status;
}

kstatus_t task_set_job_layout(task_meta_t const * const meta);

typedef struct  task {
    /* about task layouting */
    /** a task hold at most TASK_MAX_RESSOURCES_NUM regions (see memory.h backend)
       CAUTION: this field is size-impacting in kernel RAM !
    */
    layout_resource_t layout[TASK_MAX_RESSOURCES_NUM];
    uint32_t num_ressources; /* number of ressources, including txt and data */
    const task_meta_t *metadata; /**< task metadata (const, build-time, informations) */
    /*
     * Task context information, these fields store dynamic values, such as current
     * task frame, current received ipc or signal events from others, etc.
     * Only fully sched-relative infos (current quantum) are not stored in the task
     * structure but directly in the scheduler context, when the scheduler do support
     * such model (quantum-based).
     */

    taskh_t         handle;     /**< current job handle (with rerun updated) */
    stack_frame_t   *sp;        /**< current process lonely thread stack context */

    /* about events */

    /**
      Each task only has one IPC context (only blocking IPC supported).
      When sending IPC, the thread is preempted and wait for the other
      to read for its IPC content (no double user/kernel copy, only
      user-to-user blob) ensured by disabled reentrancy in kernel.
      The context hold only, for a given task, the info indicating if
      there is an IPC received and its effective size.
      When impacting the thread state (blocking IPC, the state falg
      is used)
    */
    task_event_t    ipcs;
    task_event_t    sigs;
    task_event_t    ints;

    job_state_t     state;      /**< current task state */
} task_t;

/**
 * @file task core functions private API for task manager internal
 */

task_t *task_get_table(void);

task_t *task_get_cell(taskh_t t);

void task_dump_table(void);

#endif/*!TASK_INIT_H*/
