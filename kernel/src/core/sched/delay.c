#include <inttypes.h>
#include <string.h>
#include <sentry/ktypes.h>
#include <sentry/arch/asm-generic/tick.h>
#include <sentry/managers/debug.h>
#include <sentry/sched.h>

#define CONFIG_MAX_DELAYED_JOBS (CONFIG_MAX_TASKS)

/**
 * @def RRMQ task context for a given task
 *
 * @param active: set to true of the cell hold an active task
 * @param handler: taskh_t handler for current job
 * @param priority: task priority (bigger is higher)
 * @param quantum: task quantum, in ticker (HZ) multiple
 * @param state: task state, READY in active lists, may be other state in delayed
 */
typedef struct task_delay_state {
    bool            active;
    taskh_t         handler;
    uint32_t        wait_time_ms;
} task_delay_state_t;

typedef struct delayed_jobset {
    task_delay_state_t joblist[CONFIG_MAX_TASKS];
    uint8_t num_jobs;
} delayed_jobset_t;

static delayed_jobset_t delay_ctx;

/**
 * @brief flush all events, events list is made empty
 */
kstatus_t sched_delay_flush(void)
{
    memset(&delay_ctx, 0x0, sizeof(delayed_jobset_t));
    return K_STATUS_OKAY;
}

/**
 * @brief insert a new event in the event queue
 *
 * @param event[in] the event type to add
 * @param pdata[in] associated event private data, event type specific
 * @param delay_ms[in]: event duration in ms
 * @param identifier[out]: returned identifier, when event_add succeeded
 *
 * @return:
 * - K_STATUS_OKAY on success
 * - K_ERROR_BUSY if no remaining space found
 * - K_ERROR_INVPARAM if input parameter(s) are invalid
 */
kstatus_t sched_delay_add(taskh_t job, uint32_t delay_ms)
{
    kstatus_t status;
    for (uint8_t i = 0; i < CONFIG_MAX_DELAYED_JOBS; ++i) {
        if (delay_ctx.joblist[i].active == false) {
            delay_ctx.joblist[i].handler = job;
            delay_ctx.joblist[i].wait_time_ms = delay_ms;
            delay_ctx.joblist[i].active = true;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
    status = K_ERROR_BUSY;
end:
    return status;
}

void sched_delay_tick(void)
{
    for (uint8_t i = 0; i < CONFIG_MAX_DELAYED_JOBS; ++i) {
        if (delay_ctx.joblist[i].active == true) {
            uint32_t num_ms = JIFFIES_TO_MSEC(1);
            if (likely(num_ms <= delay_ctx.joblist[i].wait_time_ms)) {
                delay_ctx.joblist[i].wait_time_ms -= num_ms;
            } else {
                delay_ctx.joblist[i].wait_time_ms = 0;
                /* delay terminated for current delayed task */
                sched_schedule(delay_ctx.joblist[i].handler);
                delay_ctx.joblist[i].active = false;
            }
        }
    }
}
