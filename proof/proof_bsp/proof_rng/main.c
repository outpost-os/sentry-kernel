#include <inttypes.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/rng/rng.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include "../framac_tools.h"

volatile uint32_t regvalue;

int main(void)
{
    uint32_t rng;

    /* as registers are volatile values, their content varies from one test to
     * another.... At a time, they will pass the framaC test
     */
    rng_probe();

    rng_get(&rng);
    rng_get(&rng);
    rng_get(&rng);
    rng_get(NULL);
    rng_get(&rng);

    return 0;
}
