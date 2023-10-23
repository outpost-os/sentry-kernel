#include <stdbool.h>
#include <uapi/handle.h>
#include <sentry/ktypes.h>
#include <sentry/arch/asm-generic/membarriers.h>

/**
 * @brief Currentky ready tasks queue
 *
 * Behave like a ring buffer to avoid any memory move.
 * Each time a task is ready (spawned, event received while not ready,
 * sleep time finished, etc.) it is pushed into the task queue, pushing
 * the 'end_of_queue' offset from one.
 * Each time a task finishes (sleep, yield, blocking wait,...)
 * it is pop'ed and schedule, pushing the 'next_task' from one.
 */
typedef struct sched_fifo_context {
    taskh_t     tasks_queue[CONFIG_MAX_TASKS]; /**< list of eligible user task of the task set */
    uint16_t    next_task;     /**< next task offset in the RB */
    uint16_t    end_of_queue;  /**< end of the RB */
    bool        empty;         /**< RB empty flag */
    taskh_t     current; /* current can be one of tasks_queue user task, or idle */
 } sched_fifo_context_t;

static sched_fifo_context_t sched_fifo_ctx;

/**
 * Probbing FIFO scheduler
 */
kstatus_t sched_fifo_probe(void)
{
    /* FIFO scheduler context is set to 0 by bss zeroification */
    sched_fifo_ctx.empty = true;
    return K_STATUS_OKAY;
}

static inline kstatus_t sched_fifo_push_task(taskh_t t)
{
    kstatus_t status = K_SECURITY_INVSTATE;
    if (unlikely((sched_fifo_ctx.next_task == sched_fifo_ctx.end_of_queue) &&
        sched_fifo_ctx.empty == false)) {
        /* should never happen if CONFIG_MAX_TASKS is valid */
        /*@ assert \false; */
        goto err;
    }
    sched_fifo_ctx.tasks_queue[sched_fifo_ctx.end_of_queue] = t;
    sched_fifo_ctx.end_of_queue = (sched_fifo_ctx.end_of_queue + 1) % CONFIG_MAX_TASKS;
    sched_fifo_ctx.empty = false;
    status = K_STATUS_OKAY;
    request_data_membarrier();
err:
    return status;
}

static inline taskh_t sched_fifo_pop_task(void)
{
    /* default task is idle */
    taskh_t t = {
        .rerun = 0,
        .id = 0xcafe, /**< reserved label for idle */
        .familly = HANDLE_TASKID,
    };
    if (likely(sched_fifo_ctx.empty == false)) {
        t = sched_fifo_ctx.tasks_queue[sched_fifo_ctx.next_task];
        sched_fifo_ctx.next_task = (sched_fifo_ctx.next_task + 1) % CONFIG_MAX_TASKS;
        if (sched_fifo_ctx.next_task == sched_fifo_ctx.end_of_queue) {
            sched_fifo_ctx.empty = true;
        }
    }
    sched_fifo_ctx.current = t;
    request_data_membarrier();
    return t;
}

kstatus_t sched_fifo_schedule(taskh_t t)
{
    return sched_fifo_push_task(t);
}

taskh_t sched_fifo_elect(void)
{
    return sched_fifo_pop_task();
}

taskh_t sched_fifo_get_current(void)
{
    return sched_fifo_ctx.current;
}

/*
 * Why not using directly schedule() ? The goal is to support, in a future model,
 * MILS architecture which may requires hierarchycal scheduling, in which, depending on
 * the task domain, the scheduling model varies. In this last case:
 *
 * each domain has a relative priority (inter-domain priority)
 * each domain has its own scheduling model
 * This allows for e.g. to:
 * execute security task in a SCHED_FIFO execution model, with a higher priority
 * than the standard tasks, executed with quantum-based RRMQ.
 * security tasks enforce their execution, but with a long enough periord between
 * each FIFO sched execution.
 * This looks a little, for e.g., like the way Linux handle POSIX RR & FIFO vs PFAIR, but
 * in a more real-time enforced model.
 * By now, as there is a single scheduler() at a time, the symbol is redirected to
 * the currently selected (and compiled) scheduler source.
 */
/* default scheduler is FIFO */
kstatus_t schedule(taskh_t t) __attribute__((alias("sched_fifo_schedule")));
taskh_t elect(void) __attribute__((alias("sched_fifo_elect")));
taskh_t sched_get_current(void) __attribute__((alias("sched_fifo_get_current")));
