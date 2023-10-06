#include <inttypes.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/exti/exti.h>


int main(void)
{
    exti_probe();
    exti_mask_interrupt(4);
    exti_unmask_interrupt(4);

    exti_mask_event(4);
    exti_unmask_event(4);

    exti_generate_swinterrupt(4);
    exti_clear_pending(4);

    return 0;
}
