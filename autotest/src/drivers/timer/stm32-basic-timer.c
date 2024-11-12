#include "timer_defs.h"
#include "stm32-basic-timer-dt.h"
#include <io.h>
#include <uapi.h>

/**
 * FIXME: prescaler config depends on timer bus (u5: APB1) clock, in order to
 * deduce the valid prescaling configuration.
 * This request (future PM enhancement) that a userspace driver can get back
 * the current IP input clock frequency to deduce properly the configuration.
 * It is, by now, hard-coded.
 */

/* hard coded 1s period for autotesting */
int timer_init(void)
{
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    uint32_t reg = 0;
    uint16_t reg16 = 0;

    /* one pulse mode */
    reg = TIM6_CR1_OPM; /* one pulse mode configured */
    iowrite32(desc->base_addr + TIM6_CR1_REG, reg);

    /* configure prescaler */
    reg16 = 610;
    iowrite16(desc->base_addr + TIM6_PSC_REG, reg16);

    /* configure counter */
    reg = 65535; /* counter value to 0xffff */
    iowrite32(desc->base_addr + TIM6_CNT_REG, reg);

    /* configure auto-relload (no dithering mode) */
    iowrite32(desc->base_addr + TIM6_ARR_REG, reg);

    reg = 0;
    /* enable interrupt update */
    reg |= TIM6_DIER_UIE;
    iowrite32(desc->base_addr + TIM6_DIER_REG, reg);
    sys_irq_enable(TIMER_IRQ);
    return 0;
}

int timer_enable(void)
{
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();

    uint32_t reg = ioread32(desc->base_addr + TIM6_CR1_REG);
    reg |= TIM6_CR1_CEN;
    iowrite32(desc->base_addr + TIM6_CR1_REG, reg);
    return 0;
}

int timer_release(void)
{
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();

    uint32_t reg = 0;
    iowrite32(desc->base_addr + TIM6_DIER_REG, reg);
    return 0;
}

int timer_enable_interrupt(void)
{
    uint32_t reg = 0;
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    /* enable interrupt update */
    reg |= TIM6_DIER_UIE;
    iowrite32(desc->base_addr + TIM6_DIER_REG, reg);
    sys_irq_enable(TIMER_IRQ);
    return 0;
}

int timer_set_periodic(void)
{
    int res = 0;
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    uint32_t reg;
    /* one pulse mode */
    reg = ioread32(desc->base_addr + TIM6_CR1_REG);
    reg &= ~TIM6_CR1_OPM;
    iowrite32(desc->base_addr + TIM6_CR1_REG, reg);
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
    uint16_t reg = 0;
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    /* clearing interrupt update flag */
    iowrite32(desc->base_addr + TIM6_SR_REG, reg);
    return 0;
}

int timer_restart(void)
{
    uint16_t reg = 0;
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    reg |= TIM6_EGR_UG;
    /* clearing interrupt update flag */
    iowrite32(desc->base_addr + TIM6_EGR_REG, reg);
    return 0;
}

Status timer_map(void)
{
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    devh_t handle;
    Status res;
    res = sys_get_device_handle(desc->label);
    if (res != STATUS_OK) {
        goto end;
    }
    copy_to_user((uint8_t*)&handle, sizeof(devh_t));
    res = sys_map_dev(handle);
    if (res != STATUS_OK) {
        goto end;
    }
end:
    return res;
}

Status timer_unmap(void)
{
    stm32_timer_desc_t const *desc = stm32_timer_get_desc();
    devh_t handle;
    Status res;
    res = sys_get_device_handle(desc->label);
    if (res != STATUS_OK) {
        goto end;
    }
    copy_to_user((uint8_t*)&handle, sizeof(devh_t));
    res = sys_unmap_dev(handle);
    if (res != STATUS_OK) {
        goto end;
    }
end:
    return res;
}
