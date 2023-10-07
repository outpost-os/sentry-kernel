#include <inttypes.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/clk/rcc.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include "../framac_tools.h"

volatile uint32_t regvalue;

int main(void)
{
    uint8_t it_or_ev = Frama_C_interval_8(0, 42);
    /* let's go, both for proof and exec :) */
    pwr_probe();
    rcc_probe();
    /*
     * read registers are volative values. FramaC consider that their value
     * change each time they are read. As function may read more than one
     * register to define their behavior, the full path coverage based on the
     * full register values possibilities is the combination of successive
     * randomly generated values of the register's fields content. This
     * requires multiple pass to reach the full coverage
     */
    for (uint8_t i = 0; i < 4; ++i) {

    }
    return 0;
}
