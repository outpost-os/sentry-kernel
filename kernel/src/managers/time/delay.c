#include <inttypes.h>
#include <string.h>
#include <sentry/ktypes.h>
#include <sentry/arch/asm-generic/tick.h>
#include <sentry/managers/debug.h>
#include <sentry/sched.h>

#define CONFIG_MAX_DELAYED_EVENTS (CONFIG_MAX_TASKS)

/**
 * @def delay queue for task-related operations
 *
 * @param active: set to true of the cell hold an active task
 * @param handler: taskh_t handler for current job
 * @param type: type of delayed action : delayed job or delayed signal
 * @param pdata: u32 pdata that may need to be delayed (sigh_t or other type of delayed action)
 * @param wait_time_ms: time to wait in miliseconds
 */
typedef struct task_delay_state {
    taskh_t           handler;
    sigh_t            sig;
    uint32_t          wait_time_ms;
    bool              active;
} task_delay_state_t;

typedef struct delayed_jobset {
    task_delay_state_t joblist[CONFIG_MAX_TASKS];
    task_delay_state_t evlist[CONFIG_MAX_DELAYED_EVENTS];
} delayed_jobset_t;

static _Alignas(uint32_t) delayed_jobset_t delay_ctx;

/**
 * @brief flush all events, events list is made empty
 */
kstatus_t mgr_time_delay_flush(void)
{
    memset(&delay_ctx, 0x0, sizeof(delayed_jobset_t));
    return K_STATUS_OKAY;
}

/**
 * @brief insert a new delayed job in the event queue
 *
 * @param job[in]: job identifier
 * @param delay_ms[in]: event duration in ms
 *
 * @return:
 * - K_STATUS_OKAY on success
 * - K_ERROR_BUSY if no remaining space found
 */
kstatus_t mgr_time_delay_add_job(taskh_t job, uint32_t delay_ms)
{
    kstatus_t status;
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
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

/**
 * @brief insert a new signal in the event queue
 *
 * @param job[in]: job identifier
 * @param delay_ms[in]: event duration in ms
 * @param sig[in]: signal to postpone
 *
 * @return:
 * - K_STATUS_OKAY on success
 * - K_ERROR_BUSY if no remaining space found
 */
kstatus_t mgr_time_delay_add_signal(taskh_t job, uint32_t delay_ms, sigh_t sig)
{
    kstatus_t status;
    for (uint8_t i = 0; i < CONFIG_MAX_DELAYED_EVENTS; ++i) {
        if (delay_ctx.joblist[i].active == false) {
            delay_ctx.joblist[i].handler = job;
            delay_ctx.joblist[i].wait_time_ms = delay_ms;
            delay_ctx.joblist[i].sig = sig;
            delay_ctx.joblist[i].active = true;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
    status = K_ERROR_BUSY;
end:
    return status;
}

/**
 * @brief Delay mechanism ticker, to be called by hardware ticker (systick....)
 */
void mgr_time_delay_tick(void)
{
    for (uint8_t i = 0; i < CONFIG_MAX_TASKS; ++i) {
        if (delay_ctx.joblist[i].active == true) {
            uint32_t num_ms = JIFFIES_TO_MSEC(1);
            if (likely(num_ms <= delay_ctx.joblist[i].wait_time_ms)) {
                delay_ctx.joblist[i].wait_time_ms -= num_ms;
            } else {
                delay_ctx.joblist[i].wait_time_ms = 0;
                /* delay terminated for current delayed task */
                mgr_task_set_state(delay_ctx.joblist[i].handler, JOB_STATE_READY);
                /* update previous NON SENSE status to OKAY now that the job is ready */
                mgr_task_set_sysreturn(delay_ctx.joblist[i].handler, STATUS_OK);
                sched_schedule(delay_ctx.joblist[i].handler);
                delay_ctx.joblist[i].active = false;
            }
        }
    }
    for (uint8_t i = 0; i < CONFIG_MAX_DELAYED_EVENTS; ++i) {
        if (delay_ctx.evlist[i].active == true) {
            uint32_t num_ms = JIFFIES_TO_MSEC(1);
            if (likely(num_ms <= delay_ctx.evlist[i].wait_time_ms)) {
                delay_ctx.evlist[i].wait_time_ms -= num_ms;
            } else {
                delay_ctx.evlist[i].wait_time_ms = 0;
                mgr_task_push_event(delay_ctx.evlist[i].sig, delay_ctx.evlist[i].handler);
                delay_ctx.evlist[i].active = false;
            }
        }
    }
}
