#include <sentry/arch/asm-cortex-m/systick.h>
#include <sentry/sched.h>
#include <sentry/managers/time.h>
#include <sentry/managers/task.h>
#include <sentry/syscalls.h>

#include <stdbool.h>

#include "../framac_tooling.h"

void handler_entrypoint(void)
{
    volatile uint32_t label = 0;

    /* security, time and task managers must be initialized first */
    mgr_security_init();
    mgr_time_init();
    mgr_task_init();
    /* handler at boot time, no scheduled tasks */
    gate_get_prochandle(&frame, label);
    return;
}
