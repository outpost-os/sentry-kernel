// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager core functions
 */

#include <inttypes.h>
#include <sentry/thread.h>
#include <sentry/managers/task.h>
#include "task_init.h"
#include "task_core.h"

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
uint32_t numtask __attribute__((used, section(".task_list.num")));


/**
 * @def table of tasks, polulated at boot time during metadata analysis
 *
 * contains all dynamic content of tasks (current sp, state...)
 * This table is sorted based on the task label (taskh_t id field) for binary search.
 * task metadata table may not.
 * This table also hold the IDLE task context, which is not a task that has been forged from
 * the upper metadata info but is a kernel local unprivilegied thread, yet holding a
 * specific task handle (i.e. with 0xCAFE mabel). Idle task has no metadata as it doesn't
 * hold any ressource (dev, shm, dma...), any capability, neither heap content or nothing,
 * but instead just do { while(1) { wfi(); yield(); }}.
 * INFO: zeroified as in .bss.
 */
static task_t task_table[CONFIG_MAX_TASKS+1];

/**
 * @brief return the local task table address
 *
 * for local manager's purpose only, exported through local header exclusively
 */
task_t *task_get_table(void)
{
    return &task_table[0];
}

/**
 * @brief return the number of declared tasks (idle excluded)
 */
uint32_t mgr_task_get_num(void)
{
    return numtask;
}

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
        uint16_t current = (left + right) >> 1;
        union u_handle h_cur;
        h_cur.h = task_table[current].metadata->handle;
        if ((h_cur.val & HANDLE_ID_MASK) > (h_arg.val & HANDLE_ID_MASK))
        {
            right = current - 1;
        } else if ((h_cur.val & HANDLE_ID_MASK) < (h_arg.val & HANDLE_ID_MASK)) {
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
kstatus_t mgr_task_get_sp(taskh_t t, stack_frame_t **sp)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(t);
    if (unlikely(tsk == NULL || sp == NULL)) {
        goto end;
    }
    *sp = tsk->sp;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @fn given a task handler, return the corresponding stack frame pointer
 *
 * binary search on task_table
 */
kstatus_t mgr_task_get_state(taskh_t t, thread_state_t *state)
{
    kstatus_t status = K_ERROR_INVPARAM;
    stack_frame_t *sp = NULL;
    task_t * tsk = task_get_from_handle(t);
    if (unlikely(tsk == NULL || state == NULL)) {
        goto end;
    }
    /*@ assert \valid(state); */
    *state = tsk->state;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @fn given a task handler, set the corresponding stack frame pointer
 */
kstatus_t mgr_task_set_sp(taskh_t t, stack_frame_t *newsp)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(t);
    if (unlikely(tsk == NULL || newsp == NULL)) {
        goto end;
    }
    /** TODO: adding security sanitation here ? or elsewhere ? */
    tsk->sp = newsp;
    status = K_STATUS_OKAY;
end:
    return status;
}

/*@
    requires thread_state_is_valid(state) == \true;
  */
kstatus_t mgr_task_set_state(taskh_t t, thread_state_t state)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(t);
    if (unlikely(tsk == NULL)) {
        goto end;
    }
    tsk->state = state;
    status = K_STATUS_OKAY;
end:
    return status;
}

secure_bool_t mgr_task_is_idletask(taskh_t t)
{
    secure_bool_t res = SECURE_FALSE;
    if (t.id == SCHED_IDLE_TASK_LABEL) {
        res = SECURE_TRUE;
    }
    return res;
}

/**
 * @fn return metadata for a given handler (const)
 */
kstatus_t mgr_task_get_metadata(taskh_t t, const task_meta_t **tsk_meta)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_meta_t const *meta = NULL;
    task_t * tsk = task_get_from_handle(t);
    if (unlikely(tsk == NULL || tsk_meta == NULL)) {
        goto end;
    }
    /*@ assert \valid(tsk_meta); */
    *tsk_meta = tsk->metadata;
    status = K_STATUS_OKAY;
end:
    return status;
}

/*
 * Forge a stack context
 */
stack_frame_t *mgr_task_initialize_sp(size_t sp, size_t pc)
{
    stack_frame_t *frame = __thread_init_stack_context(sp, pc);
    return frame;
}
