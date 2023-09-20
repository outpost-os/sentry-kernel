#include <stdbool.h>
#include <sentry/drivers/gpio/gpio.h>
#include <sentry/drivers/exti/exti.h>


int main(void)
{
    gpio_probe();
    exti_probe();
    return 0;
}
