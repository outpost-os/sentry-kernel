#include <stdbool.h>
#include <sentry/drivers/gpio/gpio.h>
#include <sentry/drivers/exti/exti.h>
#include <sentry/arch/asm-generic/platform.h>
#include <sentry/arch/asm-generic/membarriers.h>
#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/mm.h>
#include <sentry/arch/asm-cortex-m/systick.h>


int main(void)
{
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

    gpio_probe();
    exti_probe();

    return 0;
}
