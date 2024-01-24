// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager core functions
 */

#include <inttypes.h>
#include <assert.h>
#include <string.h>
#include <limits.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/arch/asm-generic/platform.h>
#include <sentry/thread.h>
#include <sentry/managers/task.h>
#include <sentry/managers/debug.h>
#include <sentry/managers/memory.h>
#include <sentry/zlib/math.h>
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
_Alignas(uint64_t) task_t task_table[CONFIG_MAX_TASKS+1];

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
 * TODO: this calculation may be done once for a task at boot time and stord
 * in task dyn data. This though required a fast taskh to task info accessor
 */
size_t mgr_task_get_data_region_size(const task_meta_t *meta)
{
    /*@ assert \valid_read(meta); */
    return CONFIG_SVC_EXCHANGE_AREA_LEN + \
           ROUND_UP(meta->got_size, __WORDSIZE) + \
           ROUND_UP(meta->data_size, __WORDSIZE) + \
           ROUND_UP(meta->bss_size, __WORDSIZE) + \
           ROUND_UP(meta->heap_size, __WORDSIZE) + \
           ROUND_UP(meta->stack_size, __WORDSIZE);
}

/**
 * TODO: this calculation may be done once for a task at boot time and stord
 * in task dyn data. This though required a fast taskh to task info accessor
 */
size_t mgr_task_get_text_region_size(const task_meta_t *meta)
{
    /*@ assert \valid_read(meta); */
    return ROUND_UP(meta->text_size, __WORDSIZE) + \
           meta->rodata_size;
    /* got and data in flash are excluded (no need) */
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
    task_t *tsk = NULL;
    for (uint8_t i = 0; i < mgr_task_get_num(); ++i) {
        if (handle_convert_to_u32(task_table[i].handle) == handle_convert_to_u32(h)) {
            tsk = &task_table[i];
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
stack_frame_t *mgr_task_initialize_sp(uint32_t rerun, size_t sp, size_t pc, size_t got)
{
    stack_frame_t *frame = __thread_init_stack_context(rerun, sp, pc, got);
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
    pc = (size_t)(idle_meta->s_text + idle_meta->entrypoint_offset);
    /* at startupt, sched return idle */
    mgr_mm_map_task(idle_meta->handle);
    /** XXX: there is a race here, if the pr_info() is not printed, a memory fault rise
        it seems that the MPU configuration take a little time before being active */
    pr_info("spawning thread, pc=%p, sp=%p", pc, sp);
    mgr_task_set_userspace_spawned();
    __platform_spawn_thread(pc, sp, THREAD_MODE_USER);
    __builtin_unreachable();
err:
    panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    __builtin_unreachable();
}


kstatus_t task_set_job_layout(task_meta_t const * const meta)
{
    kstatus_t status;
     /* mapping task data region first */
    if (unlikely(mgr_mm_map_task(meta->handle) != K_STATUS_OKAY)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    /* copy got, if non-null */
    if (likely(meta->got_size)) {
        size_t got_source = meta->s_text + \
                             ROUND_UP_TO(meta->text_size, __WORDSIZE);
        size_t got_start  = meta->s_svcexchange + \
                             CONFIG_SVC_EXCHANGE_AREA_LEN;
        pr_debug("[task handle %08x] copy %u bytes of .got from %p to %p", meta->got_size, got_source, got_start);
        memcpy((void*)got_start, (void*)got_source, meta->got_size);
    }
    /* copy data segment if non null */
    if (likely(meta->data_size)) {
        size_t data_source = meta->s_text + \
                             ROUND_UP_TO(meta->text_size, __WORDSIZE) + \
                             ROUND_UP_TO(meta->got_size, __WORDSIZE);
        size_t data_start =  meta->s_svcexchange + \
                             CONFIG_SVC_EXCHANGE_AREA_LEN + \
                             ROUND_UP_TO(meta->got_size, __WORDSIZE);
        pr_debug("[task handle %08x] copy %u bytes of .data from %p to %p", meta->data_size, data_source, data_start);
        memcpy((void*)data_start, (void*)data_source, meta->data_size);
    }
    /* zeroify bss if non-null */
    if (likely(meta->bss_size)) {
        size_t bss_start =  meta->s_svcexchange + \
                            CONFIG_SVC_EXCHANGE_AREA_LEN + \
                            ROUND_UP_TO(meta->got_size, __WORDSIZE) + \
                            ROUND_UP_TO(meta->data_size, __WORDSIZE);
        pr_debug("[task handle %08x] zeroify %u bytes of .bss at addr %p", meta->bss_size, bss_start);
        memset((void*)bss_start, 0x0, meta->bss_size);
    }
    /* zeroify SVC Exchange */
    memset((void*)meta->s_svcexchange, 0x0, CONFIG_SVC_EXCHANGE_AREA_LEN);
    status = K_STATUS_OKAY;
err:
    return status;
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

kstatus_t mgr_task_add_resource(taskh_t t, uint8_t resource_id, layout_resource_t resource)
{
    kstatus_t status;
    task_t *cell;

    if (unlikely((cell = task_get_from_handle(t)) == NULL)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }

    if (unlikely(resource_id >= TASK_MAX_RESSOURCES_NUM)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }

    memcpy(&cell->layout[resource_id], &resource, sizeof(layout_resource_t));
    status = K_STATUS_OKAY;
err:
    return status;
}

/**
 * @brief removing a resource from task context, based on its identifier
 * @warning this is the layout id, not the region id !
 */
kstatus_t mgr_task_remove_resource(taskh_t t, uint8_t resource_id)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t *cell;
    if (unlikely((cell = task_get_from_handle(t)) == NULL)) {
        goto err;
    }
    mpu_forge_unmapped_ressource(resource_id, &cell->layout[resource_id]);
    status = K_STATUS_OKAY;
err:
    return status;
}

kstatus_t mgr_task_get_layout_from_handle(taskh_t t,
                                          const layout_resource_t **layout)
{
    kstatus_t status = K_ERROR_INVPARAM;
    task_t *cell;
    if (unlikely(layout == NULL)) {
        goto err;
    }
    if (unlikely((cell = task_get_from_handle(t)) == NULL)) {
        goto err;
    }
    *layout = &cell->layout[0];
    status = K_STATUS_OKAY;
err:
    return status;
}
