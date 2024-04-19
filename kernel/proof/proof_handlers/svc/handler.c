#include <sentry/arch/asm-generic/platform.h>
#include <sentry/managers/io.h>
#include <sentry/managers/debug.h>
#include <sentry/managers/clock.h>
#include <sentry/managers/interrupt.h>
#include <sentry/managers/security.h>
#include <sentry/managers/task.h>
#include <sentry/managers/memory.h>
#include <sentry/managers/time.h>
#include <sentry/syscalls.h>

#include <stdbool.h>

#include "../framac_tooling.h"

void handler_entrypoint(void)
{
    /* security, time and task managers must be initialized first */
    mgr_clock_init();
    mgr_io_init();
    mgr_debug_init();
    mgr_security_init();
    mgr_mm_init();
    mgr_interrupt_init();
    mgr_time_init();
    mgr_task_init();
    mgr_device_init();
    platform_init();
    svc_handler(&frame);
    return;
}
