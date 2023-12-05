// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager core functions
 */

#include <inttypes.h>
#include <assert.h>
#include <string.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/arch/asm-generic/platform.h>
#include <sentry/thread.h>
#include <sentry/managers/task.h>
#include <sentry/managers/debug.h>
#include <sentry/managers/memory.h>
#include <sentry/sched.h>
#include "task_init.h"
#include "task_idle.h"
#include "task_core.h"


#ifndef TEST_MODE

/* idle task position, from linker script */
extern size_t _idle;
#endif


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
#ifndef TEST_MODE
/* in test mode, we get back the table for analysis */
static
#endif
task_t task_table[CONFIG_MAX_TASKS+1];

/**
 * @brief return the local task table address
 *
 * for local manager's purpose only, exported through local header exclusively
 */
task_t *task_get_table(void)
{
    return &task_table[0];
}

size_t mgr_task_get_data_region_size(const task_meta_t *meta)
{
    /*@ assert \valid_read(meta); */
    return CONFIG_SVC_EXCHANGE_AREA_LEN + \
           meta->data_size + (meta->data_size % SECTION_ALIGNMENT_LEN) + \
           meta->bss_size + (meta->bss_size % SECTION_ALIGNMENT_LEN) + \
           meta->heap_size + \
           meta->stack_size;
}

size_t mgr_task_get_text_region_size(const task_meta_t *meta)
{
    /*@ assert \valid_read(meta); */
    return meta->text_size + (meta->text_size % SECTION_ALIGNMENT_LEN) + \
           meta->rodata_size;
}

void task_dump_table(void)
{
#ifndef CONFIG_BUILD_TARGET_RELEASE
    /* dump all tasks including idle */
    for (uint8_t i = 0; i < mgr_task_get_num(); ++i) {
        task_t *t = &task_table[i];
        uint32_t label = t->metadata->handle.id;
        pr_debug("=== Task labeled '%02x' metainformations:", label);
        pr_debug("[%02x] --- scheduling and permissions", label);
        pr_debug("[%02x] task priority:\t\t\t%u", label, t->metadata->priority);
        pr_debug("[%02x] task quantum:\t\t\t%u", label, t->metadata->quantum);
        pr_debug("[%02x] task capabilities:\t\t\t%08x", label, t->metadata->capabilities);
        pr_debug("[%02x] --- mapping", label);
        pr_debug("[%02x] task svc_exchange section start:\t%p", label, t->metadata->s_svcexchange);
        pr_debug("[%02x] task text section start:\t\t%p", label, t->metadata->s_text);
        pr_debug("[%02x] task text section size:\t\t%u", label, t->metadata->text_size);
        pr_debug("[%02x] task rodata section size:\t\t%u", label, t->metadata->rodata_size);
        pr_debug("[%02x] task data section size:\t\t%u", label, t->metadata->data_size);
        pr_debug("[%02x] task bss section size:\t\t%u", label, t->metadata->bss_size);
        pr_debug("[%02x] task stack size:\t\t\t%u", label, t->metadata->stack_size);
        pr_debug("[%02x] task heap size:\t\t\t%u", label, t->metadata->heap_size);
        pr_debug("[%02x] task _start offset from text base:\t%u", label, t->metadata->entrypoint_offset);
    }
#endif
}

static inline task_t *task_get_from_handle(taskh_t h)
{
    uint16_t left = 0;
    /* there is numtask + 1 (idle) tasks */
    /* because of the bitfield usage and the endianess impact, we can't just use
     * a comparison of the dynamic handle, as this one may (in big endian systems)
     * not respect the numeric order initiated in the table. Instead, we find the
     * task (not the job) that match taskh_t, and then check for its current job
     */
    uint16_t right = mgr_task_get_num();
    task_t *tsk = NULL;
    uint32_t handle_norerun = handle_convert_to_u32(h) & ~HANDLE_TASK_RERUN_MASK;
    while (left < right) {
        uint16_t current = (left + right) >> 1;
        if (handle_convert_to_u32(task_table[current].metadata->handle) > handle_norerun) {
            right = (current > 0) ? current - 1 : current;
        } else if (handle_convert_to_u32(task_table[current].metadata->handle) < handle_norerun) {
            left = current + 1;
        } else {
            /* handle without rerun match, is the taskh valid for current job (rerun check) ? */
            if (handle_convert_to_u32(task_table[current].handle) ==
                handle_convert_to_u32(h)) {
                tsk = &task_table[current];
            }
            goto end;
        }
    }
end:
    return tsk;
}

secure_bool_t mgr_task_handle_exists(taskh_t h)
{
    secure_bool_t res = SECURE_FALSE;
    if (unlikely(task_get_from_handle(h) == NULL)) {
        goto end;
    }
    res = SECURE_TRUE;
end:
    return res;
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
kstatus_t mgr_task_get_state(taskh_t t, job_state_t *state)
{
    kstatus_t status = K_ERROR_INVPARAM;
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
    requires job_state_is_valid(state) == \true;
  */
kstatus_t mgr_task_set_state(taskh_t t, job_state_t state)
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

/**
 * @brief return the task handler owner of the device handler d
 *
 * @param d: the device handler to search
 * @param t: the task handler reference to update
 *
 * @return:
 *  K_STATUS_OKAY if the device is found in any of the tasks
 *  K_SECURITY_CORRUPTION if task_table is corrupted
 *  K_ERROR_NOENT if devh is not found
 */
kstatus_t mgr_task_get_device_owner(devh_t d, taskh_t *t)
{
    kstatus_t status = K_ERROR_NOENT;
    /* for all tasks... */
    for (uint8_t i = 0; i < mgr_task_get_num(); ++i) {
        if (unlikely(task_table[i].metadata == NULL)) {
            /* should not happen if init done (and thus numtask valid) */
            status = K_SECURITY_CORRUPTION;
            goto end;
        }
        /* for all devices of a task... */
        for (uint8_t dev = 0; dev < task_table[i].metadata->num_devs; ++i) {
            if (handle_convert_to_u32(task_table[i].metadata->devs[dev]) ==
                handle_convert_to_u32(d)) {
                    /* task metadata hold the same dev handle as requested */
                    memcpy(t, &task_table[i].metadata->handle, sizeof(taskh_t));
                    status = K_STATUS_OKAY;
                    goto end;
                }
        }
    }
end:
    return status;
}

/**
 * @brief starting userspace tasks
 *
 * Here, we start idle, which is responsible for directly call yield() so that
 * the scheduler will elect() the task to execute.
 *
 * This function switch to userspace and never returns.
 */
void __attribute__((noreturn)) mgr_task_start(void)
{
    stack_frame_t * sp;
    size_t pc = 0;
    const task_meta_t *idle_meta = task_idle_get_meta();
    if (unlikely(mgr_task_get_sp(idle_meta->handle, &sp) != K_STATUS_OKAY)) {
        pr_err("failed to get idle function handle!");
        goto err;
    };
#ifndef TEST_MODE
    pc = (size_t)(idle_meta->s_text + idle_meta->entrypoint_offset);
    if (unlikely(mgr_mm_map(MM_REGION_TASK_TXT, 0, idle_meta->handle) != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely(mgr_mm_map(MM_REGION_TASK_DATA, 0, idle_meta->handle) != K_STATUS_OKAY)) {
        goto err;
    }
#endif
    pr_debug("spawning thread, pc=%p, sp=%p", pc, sp);
    __platform_spawn_thread(pc, sp, THREAD_MODE_USER);

    __builtin_unreachable();
err:
    panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    __builtin_unreachable();
}



/**
 * About events manipulation in tasks
 */
kstatus_t mgr_task_push_inth_event(irqh_t ev, taskh_t t)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(t);
    job_state_t state;
    task_enqueue_event(handle_convert_to_u32(ev), &tsk->ints);
    if (likely(mgr_task_get_state(t, &state) != K_STATUS_OKAY)) {
        goto err;
    }
    if (likely(state == JOB_STATE_WAITFOREVENT)) {
        mgr_task_set_state(t, JOB_STATE_READY);
        sched_schedule(t);
    }
    status = K_STATUS_OKAY;
err:
    return status;
}


kstatus_t mgr_task_push_ipch_event(ipch_t ev, taskh_t t)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(t);
    job_state_t state;
    task_enqueue_event(handle_convert_to_u32(ev), &tsk->ipcs);
    if (likely(mgr_task_get_state(t, &state) != K_STATUS_OKAY)) {
        goto err;
    }
    if (likely(state == JOB_STATE_WAITFOREVENT)) {
        mgr_task_set_state(t, JOB_STATE_READY);
        sched_schedule(t);
    }
    status = K_STATUS_OKAY;
err:
    return status;
}

kstatus_t mgr_task_push_sigh_event(sigh_t ev, taskh_t t)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t * tsk = task_get_from_handle(t);
    job_state_t state;
    task_enqueue_event(handle_convert_to_u32(ev), &tsk->sigs);
    if (likely(mgr_task_get_state(t, &state) != K_STATUS_OKAY)) {
        goto err;
    }
    if (likely(state == JOB_STATE_WAITFOREVENT)) {
        mgr_task_set_state(t, JOB_STATE_READY);
        sched_schedule(t);
    }
    status = K_STATUS_OKAY;
err:
    return status;
}
