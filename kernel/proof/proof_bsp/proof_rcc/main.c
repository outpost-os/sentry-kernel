#include <inttypes.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/clk/rcc.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include "../framac_tools.h"

volatile uint32_t regvalue;

int main(void)
{
    uint8_t busid = Frama_C_interval_8(0, 42);
    uint32_t clkid = Frama_C_interval_32(0, 0x0a0b0c0dUL);
    uint8_t flag = Frama_C_interval_8(0, 42);
    uint32_t clk;

    /* Initialize device with randomness (over-approximation of
       all content possibilities, avoid first device access ioread32()
       uninitialized-read red alarms.
    */
    memset((void*)RCC_BASE_ADDR, Frama_C_entropy_source_32, 0x40);

    /* as registers are volatile values, their content varies from one test to
     * another.... At a time, they will pass the framaC test
     */
    rcc_probe();

    rcc_enable_apbx();
    rcc_disable_apbx();
    rcc_disable(busid, clkid, flag);
    rcc_enable(busid, clkid, flag);
    rcc_disable(busid, clkid, flag);

    rcc_get_bus_clock(busid, NULL);
    rcc_get_bus_clock(busid, &clk);

    return 0;
}
