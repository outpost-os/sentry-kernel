#include <inttypes.h>
#include <stdbool.h>
#include <ssol/io.h>
#include "platform/sync.h"

/*
 * init done flag, used like a register
 */
static uint32_t platform_early_init_done;


/**
 * @brief check if the platform initialization is done
 *
 * @see platform_init_done.
 * @return true of the platform early nitialisation is done
 */
bool platform_is_init_done(void)
{
    return (platform_early_init_done == 0xff42ff42u);
}

/**
 * @brief acknowledge the end of the platform initialization
 *
 * this should be done when the platform is in a well-known, controlled state,
 * so that various platform components (IRQ handlers, clocks, etc.) can do their
 * initialisation phase properly.
 * This also avoid any potential race conditions due to a potential dirty state
 * at the firmware bootup, generating spurious interrupts for e.g.
 */
void platform_init_done(void)
{
    iowrite32((size_t)&platform_early_init_done, 0xff42ff42u);

#if CONFIG_MODE_DEBUG
    /*
     * clean potential previous faults, typically when using jtag flashing
     */
    uint32_t cfsr = ioread32((size_t)r_CORTEX_M_SCB_CFSR);
    iowrite32((size_t)r_CORTEX_M_SCB_CFSR, cfsr | cfsr);
#endif

    request_data_membarrier();
}

void platform_spawn_kworker(void) {
    /* call arch-specific code that spawn initial kernel thread */
    __platform_spawn_kworker();
}
