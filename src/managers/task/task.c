// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager
 */

#include <inttypes.h>
#include <sentry/thread.h>
#include <sentry/task.h>

/**
 * The effective number of task is, in our case, forged by the build system
 *
 * In a model where the kernel discovers the task by checking the task section
 * in flash, this field would be upgraded by the kernel itself. Set to 0
 * at compile time, upgraded by build system in kernel ELF directly to match
 * the current project effective number of task(s)
 *
 * This allows binary search in the task list (see @ref task_table) for
 * logarithmic search time
 */
static uint16_t numtask __attribute__((used, section(".task_list.num"))) = 0;

/**
 * @def the task table store all the tasks metadata, forged by the build system
 *
 * The kernel do not set any of this table content by itself, but instead let the
 * project build system fullfill the table, by upgrading this dedicated section.
 *
 * The build system is responsible for positioning each task metadata in its cell.
 *
 * This version of the kernel only support a central task list, meaning that the
 * build system needs to:
 *   1. compile the ELF of each task, independently
 *   2. deduce, once all tasks are compiled as if they are lonely on the target,
 *      a possible mapping where all task can be placed in the flash & SRAM task section
 *      the task mapping order is based on the label list (from the smaller to the higher)
 *      so that binary search can be done on the task set below
 *   3. upgrade each task ELF based on the calculated memory mapping
 *   4. forge the task metadata from the new ELF, including HMACs, save it to a dediacted file
 *   5. store the metadata in the first free cell of the .task_list section bellow
 *
 * In a different (v2?) mode, it is  possible to consider that tasks metadata can be stored
 * in a dedicated sextion of task ELF binary instead and mapped directly in the task region.
 * In that latter case, the task mapping and boot process would be sligthly different so that
 * the kernel would 'search and copy' the tasks metadata in its own section at boot time.
 * Although, once copied, the table would store the very same content.
 */
static const task_meta_t __task_meta_table[CONFIG_MAX_TASKS] __attribute__((used, section(".task_list")));

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
 * @def table of tasks, polulated at boot time during metadata analysis
 *
 * contains all dynamic content of tasks (current sp, state...)
 * This table is sorted based on the task label (taskh_t id field) for binary search.
 * task metadata table may not.
 */
static task_t task_table[CONFIG_MAX_TASKS];

static inline task_t *task_get_from_handle(taskh_t h)
{
    uint16_t left = 0;
    union u_handle {
        uint32_t val;
        taskh_t h;
    };
    uint16_t right = CONFIG_MAX_TASKS -1;
    task_t *tsk = NULL;
    union u_handle h_arg;
    h_arg.h = h;
    while (left < right) {
        uint16_t current = (left + right) / 2;
        union u_handle h_cur;
        h_cur.h = task_table[current].metadata->handle;
        if ((h_cur.val & HANDLE_ID_MASK) > (h_arg.val & HANDLE_ID_MASK))
        {
            right = current - 1;
        } else if ((h_cur.val & HANDLE_ID_MASK) > (h_arg.val & HANDLE_ID_MASK)) {
            left = current + 1;
        } else {
            /* label do match, is the taskh valid for current label (rerun check) */
            if (h_cur.val == h_arg.val) {
                tsk = &task_table[current];
            }
            goto end;
        }
    }
end:
    return tsk;
}

/**
 * @fn given a task handler, return the corresponding stack frame pointer
 *
 * binary search on task_table
 */
stack_frame_t *task_get_sp(taskh_t t)
{
    stack_frame_t *sp = NULL;
    task_t * tsk = task_get_from_handle(t);
    if (unlikely(tsk == NULL)) {
        goto end;
    }
    sp = tsk->sp;
end:
    return sp;
}

/**
 * @fn given a task handler, set the corresponding stack frame pointer
 */
kstatus_t task_set_sp(taskh_t t, stack_frame_t *newsp)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(t);
    if (unlikely(tsk == NULL)) {
        goto end;
    }
    /** TODO: adding security sanitation here ? or elsewhere ? */
    tsk->sp = newsp;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @fn return metadata for a given handler, although in a constified form
 *
 * The lonely writter of
 */
const task_meta_t *task_get_metadata(taskh_t t)
{
    task_meta_t const *meta = NULL;
    task_t * tsk = task_get_from_handle(t);
    if (unlikely(tsk == NULL)) {
        goto end;
    }
    meta = tsk->metadata;
end:
    return meta;

}

/*
 * Forge a stack context
 */
void task_initialize_sp(size_t sp, size_t pc)
{
    __thread_init_stack_context(sp, pc);
    return;
}

/**
 * @fn initialize the task context
 *
 * Considering all the potential tasks stored in the task list, the kernel
 * analyze all the cells, check for the metadata and the task integrity and
 * then initialize the task context (data copy, bss zeroification).
 * All tasks that are schedulable at bootup are added to the scheduler queue
 * (call to the sched_schedule() function).
 * The task init do NOT call sched_elect() neither spawn any thread directly.
 * It only prepare the overall task-set in association with the scheduler so
 * that the OS is ready to enter nominal mode.
 *
 * @return K_STATUS_OKAY if all tasks found are clear (I+A), or K_SECURITY_INTEGRITY
 *  if any HMAC calculation fails
 */
kstatus_t task_init(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}


/**
 * @fn function that can be called periodically by external security watchdog
 *
 * This function recalculate the metadata integrity (and can recalculate the
 * task .text+rodata potentially)
 */
kstatus_t task_watchdog(void)
{
    return K_STATUS_OKAY;
}
