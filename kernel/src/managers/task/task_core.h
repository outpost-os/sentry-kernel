// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef TASK_CORE_H
#define TASK_CORE_H

/**
 * @file task core functions private API for task manager internal
 */

#include <uapi/uapi.h>
#include <sentry/managers/task.h>
#include <sentry/arch/asm-generic/memory.h>

#define TASK_EVENT_QUEUE_DEPTH 16

#define HANDLE_TASKID 0x0UL

typedef struct __attribute__((packed)) ktaskh  {
    uint32_t rerun : 20;
    uint32_t id : 8;
    uint32_t family : 3;
} ktaskh_t;

static_assert(sizeof(ktaskh_t) == sizeof(taskh_t), "taskh_t opaque model failure!");

static inline const ktaskh_t *taskh_to_ktaskh(const taskh_t * const th) {
    /*@ assert \valid(th); */
    union uth {
        const uint32_t *th;
        const ktaskh_t *kth;
    };

    union uth converter = {
        .th = th
    };
    return converter.kth;
}

static inline const taskh_t *ktaskh_to_taskh(const ktaskh_t * const kth) {
    /*@ assert \valid(kth); */
    union uth {
        const uint32_t *th;
        const ktaskh_t *kth;
    };

    union uth converter = {
        .kth = kth
    };
    return converter.th;
}

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

    ktaskh_t        handle;     /**< current job handle (with rerun updated) */
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
    uint32_t           ipcs[CONFIG_MAX_TASKS];       /**< List of IPCs event (one per peer task) */
    uint32_t           sigs[CONFIG_MAX_TASKS];       /**< List of SIGs event (one per peer task) */
    uint32_t           ints[TASK_EVENT_QUEUE_DEPTH]; /**< List of IRQ events */
    uint8_t            num_ints;

    job_state_t     state;      /**< current task state */
    secure_bool_t   sysretassigned; /**< a syscall has assigned a sysreturn */
    Status          sysreturn;  /**< current job syscall return */
} task_t;


kstatus_t task_set_job_layout(task_t * const tsk);

task_t *task_get_table(void);

task_t *task_get_from_handle(taskh_t h);

void task_dump_table(void);

#endif/*!TASK_INIT_H*/
