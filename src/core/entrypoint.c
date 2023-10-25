#include <inttypes.h>
#include <stdbool.h>

/* kernel includes */
#include <sentry/arch/asm-generic/platform.h>
#include <sentry/arch/asm-generic/membarriers.h>
#include <sentry/mm.h>
#include <bsp/drivers/gpio/gpio.h>
#if CONFIG_ARCH_ARM_CORTEX_M
#include <sentry/arch/asm-cortex-m/systick.h>
#else
#error "unsupported platform"
#endif
#include <sentry/managers/io.h>
#include <sentry/managers/debug.h>
#include <sentry/managers/clock.h>
#include <sentry/managers/interrupt.h>
#include <sentry/managers/security.h>
#include <sentry/thread.h>


/*
 * address if the PSP idle stack, as defined in the layout (see m7fw.ld)
 */

#if __GNUC__
#if __clang__
# pragma clang optimize off
#else
__attribute__((optimize("-fno-stack-protector")))
#endif
#endif
__attribute__((noreturn)) void _entrypoint(void)
{
    /* early init phase */
    mgr_interrupt_early_init();

    /* init phase */
    mgr_clock_init();
    mgr_interrupt_init();
    mgr_io_init();
    mgr_debug_init();

    pr_info("Starting Sentry kernel release %s", "v0.1");
    pr_info("booting on SoC %s", CONFIG_ARCH_SOCNAME);
    pr_info("configured dts file: %s", CONFIG_DTS_FILE);
    /* end of basic platform initialization acknowledged */
    platform_init();
    pr_info("Platform initialization done, continuing with upper layers");
    mgr_security_init();

#if 0 /* FIXME */
    systick_init();
#endif


#if CONFIG_USE_SSP
    /* TODO initialize SSP with random seed */
#endif
    /* initialize memory backend controler (e.g. MPU )*/
#if 0 /* FIXME */
    mm_initialize();
    mm_configure();
#endif

#if 0
#if defined(CONFIG_USE_ICACHE) && (CONFIG_USE_ICACHE == 1)
    icache_enable();
#endif

#if defined(CONFIG_USE_DCACHE) && (CONFIG_USE_DCACHE == 1)
    dcache_enable();
#endif


    // init systick
    set_core_frequency();

    perfo_early_init();
#endif

#if 0 /* FIXME */
    systick_init();
    mgr_io_probe();
#endif

    do {
        asm volatile("wfi");
    } while (1);
    __builtin_unreachable();
    /* This part of the function is never reached */
}
