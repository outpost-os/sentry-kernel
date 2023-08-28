#if 0
#include <board.h>
#include <arch/cache.h>
#include <arch/mpu.h>
#include <arch/perfo.h>
#include <usleep.h>
#endif
#include <inttypes.h>

/* kernel includes */
#include <arch/asm-generic/thread.h>
#include <arch/asm-generic/platform.h>
#include <arch/asm-generic/membarriers.h>
#include <arch/asm-generic/interrupt.h>

#if 0
#include "layout.h"
#include "clock.h"
#include "platform/nvic.h"
#include "platform/arm_semihosting.h"
#include "platform/systick.h"
#include "platform/init.h"
#include "platform/scb.h"
#include "framebuffer.h"
#include "devices/edma.h"
#include "devices/gpc.h"
#include "devices/mipi_dsi.h"
#include "devices/lcdif3.h"
#include "devices/ccm.h"
#include "devices/ecspi.h"
#include "devices/audioblockctrl.h"
#include "devices/mediablockctrl.h"

#include "workqueue.h"
#include "secureelem.h"

#include "mu_client.h"
#endif

//#include <ssol/io.h>

/*
 * address if the PSP idle stack, as defined in the layout (see m7fw.ld)
 */
extern uint32_t _idlestack;
static uint32_t* idle_stack_pointer = (uint32_t*)&_idlestack;



extern uint32_t platform_early_init_done;;

#if __GNUC__
#if __clang__
# pragma clang optimize off
#else
__attribute__ ((optimize("-fno-stack-protector")))
#endif
#endif
int _entrypoint(void)
{
    interrupt_disable();

    interrupt_init();

    platform_init();
    systick_init();

#if 0
// TODO
    /*
     * enable usleep(). Needs to be reexecuted after
     * core frequency upda to upgrade the usleep cycle per USEC_PER_SEC
     * calculation
     */
    perfo_init();

    clock_init();



    /* About CM7 clocking. TBD in IMX8MP (dunno companion mode model)*/
#endif

#if CONFIG_USE_SSP
    /* TODO initialize SSP with random seed */
#endif

#if 0
// TODO
#if defined(CONFIG_USE_ICACHE) && (CONFIG_USE_ICACHE == 1)
    if (icache_is_enabled()) {
       icache_disable();
    }
#endif

#if defined(CONFIG_USE_DCACHE) && (CONFIG_USE_DCACHE == 1)
    if (dcache_is_enabled()) {
       dcache_disable();
    }
#endif
#endif

    /* initialize memory backend controler (e.g. MPU )*/
    mm_initialize();
    mm_configure();

#if 0
#if defined(CONFIG_USE_ICACHE) && (CONFIG_USE_ICACHE == 1)
    icache_enable();
#endif

#if defined(CONFIG_USE_DCACHE) && (CONFIG_USE_DCACHE == 1)
    dcache_enable();
#endif


    // init systick
    set_core_frequency();
    systick_init();
    perfo_early_init();
#endif

    platform_spawn_kworker();

    /* This part of the function is never reached */

    return 0;
}
