#include <inttypes.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/clk/pwr.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include "../framac_tools.h"

volatile uint32_t regvalue;

int main(void)
{
    pwr_probe();
    return 0;
}
