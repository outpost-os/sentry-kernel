// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager init automaton functions
 */
#include <string.h>
#include <inttypes.h>
#include <sentry/thread.h>
#include <sentry/managers/task.h>
#include <sentry/managers/debug.h>
#include <sentry/managers/memory.h>
#include <sentry/sched.h>
#include <sentry/arch/asm-generic/membarriers.h>
#include <sentry/arch/asm-generic/platform.h>

#include "task_core.h"
#include "task_init.h"
#include "task_idle.h"

#ifndef TEST_MODE
extern size_t _idle;
#else
extern void (ut_idle)(void);
#endif

typedef enum task_mgr_state {
    TASK_MANAGER_STATE_BOOT = 0x0UL,                /**< at boot time */
    /* for each cell of task_meta_table */
    TASK_MANAGER_STATE_DISCOVER_SANITATION, /**<  magic & version check */
    TASK_MANAGER_STATE_CHECK_META_INTEGRITY,/**< metadata HMAC check */
    TASK_MANAGER_STATE_CHECK_TSK_INTEGRITY, /**< task HMAC check */
    TASK_MANAGER_STATE_INIT_LOCALINFO,      /**< init dynamic task info into local struct */
    TASK_MANAGER_STATE_TSK_MAP,             /**< task data copy, bss zeroify, stack init */
    TASK_MANAGER_STATE_TSK_SCHEDULE,        /**< schedule task (if start at bootup) */
    TASK_MANAGER_STATE_FINALIZE,            /**< all tasks added, finalize (sort task list) */
    TASK_MANAGER_STATE_READY,               /**< ready state, everything is clean */
    TASK_MANAGER_STATE_ERROR_SECURITY,      /**< hmac or magic error */
    TASK_MANAGER_STATE_ERROR_RUNTIME,       /**< others (sched...) */
} task_mgr_state_t;

struct task_mgr_ctx {
    task_mgr_state_t state;
    uint16_t         numtask;
    kstatus_t        status;
};

static struct task_mgr_ctx ctx;


static inline void task_swap(task_t *t1, task_t *t2)
{
    task_t pivot;
    memcpy(&pivot, t2, sizeof(task_t));
    memcpy(t2, t1, sizeof(task_t));
    memcpy(t1, &pivot, sizeof(task_t));
}

static inline void task_basic_sort(task_t *table)
{
    uint16_t i, j;
    for (i = 0; i < mgr_task_get_num()+1; i++) {
        for (j = 0; j < mgr_task_get_num() - i; j++) {
            /** INFO: task table is configured to CONFIG_MAX_TASKS+1 to handle idle, j+1 always valid */
            if (table[j].metadata->handle.id > table[j+1].metadata->handle.id) {
                task_swap(&table[j], &table[j + 1]);
            }
        }
    }
}

#ifndef TEST_MODE
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
#else
/* UT provided */
const task_meta_t *ut_get_task_meta_table(void);
#define __task_meta_table ut_get_task_meta_table()
#endif

/**
 * @brief discover_sanitation state handling
 *
 * must be executed in TASK_MANAGER_STATE_DISCOVER_SANITATION state.
 * Move to TASK_MANAGER_STATE_CHECK_META_INTEGRITY only on success, or move to
 * TASK_MANAGER_STATE_ERROR_SECURITY otherwise.
 */
static inline kstatus_t task_init_discover_sanitation(task_meta_t const * const meta)
{
    kstatus_t status = K_SECURITY_INTEGRITY;
    /* entering state check */
    if (unlikely(ctx.state != TASK_MANAGER_STATE_DISCOVER_SANITATION)) {
        pr_err("invalid state!");
        ctx.state = TASK_MANAGER_STATE_ERROR_SECURITY;
        goto end;
    }
    if (unlikely(meta->magic != CONFIG_TASK_MAGIC_VALUE)) {
        ctx.state = TASK_MANAGER_STATE_ERROR_SECURITY;
        pr_err("invalid magic value found %llu", meta->magic);
        goto end;
    }
    pr_info("[task handle %08x] sanitation ok", meta->handle);
    /* TODO version handling */
    ctx.state = TASK_MANAGER_STATE_CHECK_META_INTEGRITY;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief check_meta_integrity state handling
 *
 * must be executed in TASK_MANAGER_STATE_CHECK_META_INTEGRITY state.
 * Move to TASK_MANAGER_STATE_CHECK_TSK_INTEGRITY only on success, or move to
 * TASK_MANAGER_STATE_ERROR_SECURITY otherwise.
 */
static inline kstatus_t task_init_check_meta_integrity(task_meta_t const * const meta)
{
    kstatus_t status = K_SECURITY_INTEGRITY;
    /* entering state check */
    if (unlikely(ctx.state != TASK_MANAGER_STATE_CHECK_META_INTEGRITY)) {
        pr_err("invalid state!");
        ctx.state = TASK_MANAGER_STATE_ERROR_SECURITY;
        goto end;
    }
    /* FIXME: call the hmac service in order to validate metadata integrity,
       and return the result */
    pr_info("[task handle %08x] metadata integrity ok", meta->handle);
    ctx.state = TASK_MANAGER_STATE_CHECK_TSK_INTEGRITY;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief check_tsk_integrity state handling
 *
 * must be executed in TASK_MANAGER_STATE_CHECK_TSK_INTEGRITY state.
 * Move to TASK_MANAGER_STATE_INIT_LOCALINFO only on success, or move to
 * TASK_MANAGER_STATE_ERROR_SECURITY otherwise.
 */
static inline kstatus_t task_init_check_tsk_integrity(task_meta_t const * const meta)
{
    kstatus_t status = K_SECURITY_INTEGRITY;
    /* entering state check */
    if (unlikely(ctx.state != TASK_MANAGER_STATE_CHECK_TSK_INTEGRITY)) {
        pr_err("invalid state!");
        ctx.state = TASK_MANAGER_STATE_ERROR_SECURITY;
        goto end;
    }
    /* FIXME: call the hmac service in order to validate metadata integrity,
       and return the result */
    pr_info("[task handle %08x] task code+data integrity ok", meta->handle);
    ctx.state = TASK_MANAGER_STATE_INIT_LOCALINFO;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief local info writting state handling
 *
 * must be executed in TASK_MANAGER_STATE_INIT_LOCALINFO state.
 * Move to TASK_MANAGER_STATE_TSK_MAP only on success, or move to
 * TASK_MANAGER_STATE_ERROR_SECURITY otherwise.
 */
static inline kstatus_t task_init_initiate_localinfo(task_meta_t const * const meta)
{
    kstatus_t status = K_SECURITY_INTEGRITY;
    task_t * task_table = task_get_table();
    uint16_t cell = ctx.numtask;

    /* entering state check */
    if (unlikely(ctx.state != TASK_MANAGER_STATE_INIT_LOCALINFO)) {
        pr_err("invalid state!");
        ctx.state = TASK_MANAGER_STATE_ERROR_SECURITY;
        goto end;
    }
    if (unlikely(cell == CONFIG_MAX_TASKS+1)) {
        ctx.state = TASK_MANAGER_STATE_ERROR_SECURITY;
        goto end;
    }
    /* forge local info, push back current and next afterward */
    task_table[cell].metadata = meta;
    /* stack top is calculated from layout forge. We align each section to SECTION_ALIGNMENT_LEN to
     * ensure HW constraint word alignment if not already done at link time (yet should be zero) */
    size_t stack_top = meta->s_svcexchange + mgr_task_get_data_region_size(meta);
    task_table[cell].sp = mgr_task_initialize_sp(stack_top, (meta->s_text + meta->entrypoint_offset));
    pr_info("[task handle %08x] task local dynamic content set", meta->handle);
    /* TODO: ipc & signals ? nothing to init as memset to 0 */
    ctx.state = TASK_MANAGER_STATE_TSK_MAP;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief task memory mapping state handling
 *
 * must be executed in TASK_MANAGER_STATE_TSK_MAP state.
 * Move to TASK_MANAGER_STATE_TSK_SCHEDULE only on success, or move to
 * TASK_MANAGER_STATE_ERROR_SECURITY otherwise.
 */
static inline kstatus_t task_init_map(task_meta_t const * const meta)
{
    /* entering state check */
    kstatus_t status;
    if (unlikely(ctx.state != TASK_MANAGER_STATE_TSK_MAP)) {
        pr_err("invalid state!");
        ctx.state = TASK_MANAGER_STATE_ERROR_SECURITY;
        status = K_SECURITY_CORRUPTION;
        goto err;
    }
    /* mapping task data region first */
    if (unlikely(mgr_mm_map(MM_REGION_TASK_DATA, 0, meta->handle) != K_STATUS_OKAY)) {
        status = K_ERROR_MEMFAIL;
        goto err;
    }
    /* configure its content */
    if (likely(meta->data_size)) {
        size_t data_source = meta->s_text + \
                             meta->text_size + \
                             meta->text_size % SECTION_ALIGNMENT_LEN + \
                             meta->rodata_size + \
                             meta->rodata_size % SECTION_ALIGNMENT_LEN;
        size_t data_start =  meta->s_svcexchange + \
                            CONFIG_SVC_EXCHANGE_AREA_LEN;
        pr_debug("[task handle %08x] copy %u bytes of .data from %p to %p", meta->data_size, data_source, data_start);
        memcpy((void*)data_source, (void*)data_start, meta->data_size);
    }
    if (likely(meta->bss_size)) {
        size_t bss_start =  meta->s_svcexchange + \
                            CONFIG_SVC_EXCHANGE_AREA_LEN + \
                            meta->data_size + (meta->data_size % SECTION_ALIGNMENT_LEN);
        pr_debug("[task handle %08x] zeroify %u bytes of .bss at addr %p", meta->bss_size, bss_start);
        memset((void*)bss_start, 0x0, meta->bss_size);
    }
    /* unmap task data */
    if (unlikely(mgr_mm_unmap(MM_REGION_TASK_DATA, 0, meta->handle) != K_STATUS_OKAY)) {
        status = K_ERROR_MEMFAIL;
        goto err;
    }
    pr_info("[task handle %08x] task memory map forged", meta->handle);
    ctx.state = TASK_MANAGER_STATE_TSK_SCHEDULE;
    status = K_STATUS_OKAY;
err:
    return status;
}

/**
 * @brief task scheduling handling
 *
 * must be executed in TASK_MANAGER_STATE_TSK_SCHEDULE state.
 * Move to TASK_MANAGER_STATE_DISCOVER_SANITATION if success and still some
 * tasks to analyze in the meta tab, or move to TASK_MANAGER_STATE_FINALIZE if
 * that was the tast task. Move to TASK_MANAGER_STATE_ERROR_SECURITY in case of
 * error.
 */
static inline kstatus_t task_init_schedule(task_meta_t const * const meta,
                                           task_mgr_state_t last_loop_state)
{
    kstatus_t status = K_STATUS_OKAY;
    /* entering state check */
    if (unlikely(ctx.state != TASK_MANAGER_STATE_TSK_SCHEDULE)) {
        pr_err("invalid state!");
        ctx.state = TASK_MANAGER_STATE_ERROR_SECURITY;
        goto end;
    }
    if (meta->flags.start_mode == JOB_FLAG_START_AUTO) {
        status = sched_schedule(meta->handle);
        if (unlikely(status != K_STATUS_OKAY)) {
            ctx.state = TASK_MANAGER_STATE_ERROR_RUNTIME;
            goto end;
        }
        pr_info("[task handle {%04x|%04x|%03x}] task forged", meta->handle.rerun, meta->handle.id, meta->handle.family);
    }
    ctx.numtask++;
    ctx.state = last_loop_state;
end:
    return status;
}


/**
 * @brief finalize the task table construct
 *
 * add the idle task to the local tasks table
 * ordering it based on the label identifier (handle->id value).
 */
static inline kstatus_t task_init_finalize(void)
{
    task_t * task_table = task_get_table();

    /* entering state check */
    if (unlikely(ctx.state != TASK_MANAGER_STATE_FINALIZE)) {
        pr_err("invalid state!");
        ctx.status = K_SECURITY_INTEGRITY;
        goto end;
    }
    /* adding idle task to list */
    task_meta_t *meta = task_idle_get_meta();
    /* should we though forge a HMAC for idle metadata here ? */
    task_table[ctx.numtask].metadata = meta;
    task_table[ctx.numtask].handle = meta->handle;
    size_t idle_sp = meta->s_svcexchange + mgr_task_get_data_region_size(meta);
#ifndef TEST_MODE
    task_table[ctx.numtask].sp = mgr_task_initialize_sp(idle_sp, (size_t)&_idle);
#else
    /* in UT mode, idle is mocked */
    task_table[ctx.numtask].sp = mgr_task_initialize_sp(idle_sp, (size_t)ut_idle);
#endif

    pr_info("[task handle {%04x|%04x|%03x}] idle task forged",
        (uint32_t)meta->handle.rerun, (uint32_t)meta->handle.id, (uint32_t)meta->handle.family);
    ctx.numtask++;
    /* idle is not scheduled, it is instead a fallback of all schedulers, using its handler
     * at election time only
     */
    /* finishing with sorting task_table based on task label value */
    task_basic_sort(task_table);
    pr_info("task list ordered based on label");
    pr_info("found a total of %u tasks, including idle", ctx.numtask);
    ctx.status = K_STATUS_OKAY;
    ctx.state = TASK_MANAGER_STATE_READY;
end:
    return ctx.status;
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
kstatus_t mgr_task_init(void)
{
    ctx.state = TASK_MANAGER_STATE_BOOT;
    ctx.numtask = 0; /* at the end, before adding idle task, must be equal
                        to buildsys set number of tasks */
    ctx.status = K_STATUS_OKAY;
    pr_info("init idletask metadata");
    task_idle_init();
    pr_info("starting task initialization, max allowed tasks: %u", CONFIG_MAX_TASKS);
    /* first zeroify the task table (JTAG reflush case) */
    task_t * task_table = task_get_table();
    memset(task_table, 0x0, (CONFIG_MAX_TASKS+1)*sizeof(task_t));


    if (mgr_task_get_num() == 0) {
        ctx.state = TASK_MANAGER_STATE_FINALIZE;
    } else {
        ctx.state = TASK_MANAGER_STATE_DISCOVER_SANITATION;
    }
    task_mgr_state_t last_loop_state;
    /* for all tasks, discover, analyse, and init */
    for (uint16_t cell = 0; cell < mgr_task_get_num(); ++cell) {
        if (cell+1U == mgr_task_get_num()) {
            last_loop_state = TASK_MANAGER_STATE_FINALIZE;
        } else {
            last_loop_state = TASK_MANAGER_STATE_DISCOVER_SANITATION;
        }
        pr_info("starting task blob %u/%u checks", cell+1, mgr_task_get_num());
        ctx.status = task_init_discover_sanitation(&__task_meta_table[cell]);
        if (unlikely(ctx.status != K_STATUS_OKAY)) {
            goto end;
        }
        ctx.status = task_init_check_meta_integrity(&__task_meta_table[cell]);
        if (unlikely(ctx.status != K_STATUS_OKAY)) {
            goto end;
        }
        ctx.status = task_init_check_tsk_integrity(&__task_meta_table[cell]);
        if (unlikely(ctx.status != K_STATUS_OKAY)) {
            goto end;
        }
        ctx.status = task_init_initiate_localinfo(&__task_meta_table[cell]);
        if (unlikely(ctx.status != K_STATUS_OKAY)) {
            goto end;
        }
        ctx.status = task_init_map(&__task_meta_table[cell]);
        if (unlikely(ctx.status != K_STATUS_OKAY)) {
            goto end;
        }
        ctx.status = task_init_schedule(&__task_meta_table[cell], last_loop_state);
        if (unlikely(ctx.status != K_STATUS_OKAY)) {
            goto end;
        }
    }
    /* finalize, adding idle task */
    task_init_finalize();

    task_dump_table();
end:
    return ctx.status;
}


/**
 * @fn function that can be called periodically by external security watchdog
 *
 * This function recalculate the metadata integrity (and can recalculate the
 * task .text+rodata potentially)
 */
kstatus_t mgr_task_watchdog(void)
{
    return K_STATUS_OKAY;
}
