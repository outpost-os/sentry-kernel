

#ifndef __STM32X4_PLL_H
#define __STM32X4_PLL_H

#if !defined(CONFIG_SOC_SUBFAMILY_STM32L4) && !defined(CONFIG_SOC_SUBFAMILY_STM32F4)
#error "this header should not be included in SoCs others than STM32F4/STM32L4 family"
#endif /* !defined(CONFIG_SOC_SUBFAMILY_STM32L4) && !defined(CONFIG_SOC_SUBFAMILY_STM32F4) */

#include <sentry/ktypes.h>

/*
 * PLL output clock gating is available only on stm32l4 family
 */
#if defined(CONFIG_SOC_SUBFAMILY_STM32L4)

/*
 * XXX:
 *  As it is quite hackish to have this file in `include/bsp/drivers`
 *  make sure to include rcc register definition (svd based `rcc-defs.h`) before this file
 */

__STATIC_INLINE void stm32l4_enable_pll_output(uint32_t en_bit)
{
    uint32_t pllcfg = ioread32(RCC_BASE_ADDR + RCC_PLLCFGR_REG);
    pllcfg |= en_bit;
    iowrite32(RCC_BASE_ADDR + RCC_PLLCFGR_REG, pllcfg);
}

__STATIC_INLINE void stm32l4_enable_pll_p_output(void)
{
    stm32l4_enable_pll_output(RCC_PLLCFGR_PLLPEN);
}

__STATIC_INLINE void stm32l4_enable_pll_q_output(void)
{
    stm32l4_enable_pll_output(RCC_PLLCFGR_PLLQEN);
}

__STATIC_INLINE void stm32l4_enable_pll_r_output(void)
{
    stm32l4_enable_pll_output(RCC_PLLCFGR_PLLREN);
}

__STATIC_INLINE void stm32l4_disable_pll_output(uint32_t en_bit)
{
    uint32_t pllcfg = ioread32(RCC_BASE_ADDR + RCC_PLLCFGR_REG);
    pllcfg &= ~en_bit;
    iowrite32(RCC_BASE_ADDR + RCC_PLLCFGR_REG, pllcfg);
}

__STATIC_INLINE void stm32l4_disable_pll_p_output(void)
{
    stm32l4_disable_pll_output(RCC_PLLCFGR_PLLPEN);
}

__STATIC_INLINE void stm32l4_disable_pll_q_output(void)
{
    stm32l4_disable_pll_output(RCC_PLLCFGR_PLLQEN);
}

__STATIC_INLINE void stm32l4_disable_pll_r_output(void)
{
    stm32l4_disable_pll_output(RCC_PLLCFGR_PLLREN);
}

#endif

/**
 * @brief Enable stm32f4xx/stm32l4xx main pll
 *
 * @note stm32l4xx only: P/Q/R outputs need to be enable independently and after PLL start
 *
 * @return K_STATUS_OKAY in case of success.
 *         K_ERROR_ENOENT if there no such PLL available (i.e. dts node w/ `status=disabled` or no compatible node )
 *         K_ERROR_NOTREADY otherwise.
 */
kstatus_t stm32x4_enable_pll(void);

#endif /* __STM32X4_PLL_H */
