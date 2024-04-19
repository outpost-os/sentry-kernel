#include <sentry/arch/asm-cortex-m/systick.h>
#include <sentry/sched.h>
#include <sentry/managers/time.h>
#include <sentry/managers/task.h>

#include <stdbool.h>

#include "../framac_tooling.h"

void handler_entrypoint(void)
{
    taskh_t autotest_handle;

    /* security, time and task managers must be initialized first */
    mgr_security_init();
    mgr_time_init();
    mgr_task_init();
    /* handler at boot time, no scheduled tasks */
    systick_handler(&frame);
    /* add autotest to scheduler */
    if (mgr_task_get_handle(SCHED_AUTOTEST_TASK_LABEL, &autotest_handle) != K_STATUS_OKAY) {
        goto end;
    }
    sched_schedule(autotest_handle);
    /* tick again */
    systick_handler(&frame);
    /* add content to sleep manager */
    mgr_time_delay_add_job(autotest_handle, Frama_C_interval_u32(0,3));
    /* tick again */
    systick_handler(&frame);
end:
    return;
}
