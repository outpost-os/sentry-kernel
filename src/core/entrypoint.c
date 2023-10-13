#include <inttypes.h>
#include <stdbool.h>

/* kernel includes */
#include <sentry/arch/asm-generic/platform.h>
#include <sentry/arch/asm-generic/membarriers.h>
#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/mm.h>
#include <bsp/drivers/clk/rcc.h>
#include <bsp/drivers/clk/pwr.h>
#include <bsp/drivers/flash/flash.h>
#include <bsp/drivers/gpio/gpio.h>
#include <bsp/drivers/usart/usart.h>
#if CONFIG_ARCH_ARM_CORTEX_M
#include <sentry/arch/asm-cortex-m/systick.h>
#else
#error "unsupported platform"
#endif
#include <sentry/managers/io.h>
#include <bsp/drivers/rng/rng.h>
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
    interrupt_disable();
    mgr_io_probe();
    interrupt_init();
    pwr_probe();
    flash_probe();
    rcc_probe();

    interrupt_init();

    platform_init();
#if 0 /* FIXME */
    systick_init();
#endif

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

    /* XXX: TODO */
    gpio_probe(0);
    gpio_probe(1);
    gpio_probe(2);
    gpio_probe(3);
    gpio_probe(4);
    gpio_probe(5);
    gpio_probe(6);

#if CONFIG_BUILD_TARGET_DEBUG
    rcc_enable_debug_clockout();
#endif

    usart_probe();
    usart_tx("coucou\n",7);

    // init ssp

/*
 * XXX: TODO
 *  Use a Kconfig selector to explicitly enable driver and rgn support
 *  maybe a DTS property for the 'chosen' entropy source.
 */
#if !defined(CONFIG_ARCH_MCU_STM32F401)
    uint32_t seed;
    rng_probe();
    rng_get(&seed);
#endif

    do {
        asm volatile("wfi");
    } while (1);
    __builtin_unreachable();
    /* This part of the function is never reached */
}
