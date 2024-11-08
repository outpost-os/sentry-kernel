#include "timer_defs.h"
#include "stm32-basic-timer-dt.h"
#include <io.h>

/* hard coded 1s period for autotesting */
int timer_init(void)
{
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    uint32_t reg = 0;
    uint16_t reg16 = 0;

    /* configure counter+prescaler */
    reg = 65535; /* counter value to 0xffff */
    iowrite32(desc->base_addr + TIM6_CNT_REG, reg);

    /* configure counter+prescaler */
    reg16 = 610;
    iowrite16(desc->base_addr + TIM6_PSC_REG, reg16);

    reg = 0;
    /* enable interrupt update */
    reg |= TIM6_DIER_UIE;
    iowrite32(desc->base_addr + TIM6_DIER_REG, reg);
    return 0;
}

int timer_enable(void)
{
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();

    uint32_t reg = 0;
    reg |= TIM6_CR1_CEN;
    iowrite32(desc->base_addr + TIM6_DIER_REG, reg);
    return 0;
}

int timer_release(void)
{
    return 0;
}

int timer_enable_interrupt(void)
{
    uint32_t reg = 0;
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    /* enable interrupt update */
    reg |= TIM6_DIER_UIE;
    iowrite32(desc->base_addr + TIM6_DIER_REG, reg);
    return 0;
}

int timer_disable_interrupt(void)
{
    uint32_t reg = 0;
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    /* disable interrupt update */
    iowrite32(desc->base_addr + TIM6_DIER_REG, reg);
    return 0;
}

int timer_interrupt_acknowledge(void)
{
    uint32_t reg = 0;
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    /* clearing interrupt update flag */
    iowrite32(desc->base_addr + TIM6_SR_REG, reg);
    return 0;
}
