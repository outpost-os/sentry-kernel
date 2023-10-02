#include <stdbool.h>
#include <sentry/arch/asm-generic/platform.h>
#include <sentry/arch/asm-generic/membarriers.h>
#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/mm.h>
#include <sentry/arch/asm-cortex-m/systick.h>
#include <sentry/managers/io.h>

int main(void)
{
    uint32_t val;
    interrupt_disable();


    clk_reset();
    /* initial PLLs: HSI mode, enable PLL clocks. FIXME: use KConfig instead */
    clk_set_system_clk(false, true);

    interrupt_init();
    platform_init();
    perfo_init();
    clock_init();
    mm_initialize();
    mm_configure();

    set_core_frequency();
    systick_init();
    perfo_early_init();

    /* start calling managers */
    mgr_io_probe();

    rng_probe();
    rng_load(&val);

    return 0;
}
