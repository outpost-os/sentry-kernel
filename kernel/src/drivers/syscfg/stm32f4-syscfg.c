// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file STM32F3xx and F4xx PLL & clock driver (see ST RM0090 datasheet)
 */
#include <assert.h>
#include <stdbool.h>
#include <stdatomic.h>

#include <sentry/arch/asm-cortex-m/soc.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/managers/memory.h>
#include <sentry/io.h>
#include <sentry/bits.h>
#include <sentry/ktypes.h>
#include <sentry/zlib/crypto.h>
#include "syscfg_defs.h"
#include "stm32-syscfg-dt.h"

#if defined(CONFIG_ARCH_MCU_STM32F439) || defined(CONFIG_ARCH_MCU_STM32F429)
# define MAX_EXTI_GPIO_PORT  'J'
#elif defined(CONFIG_ARCH_MCU_STM32F419)
# define MAX_EXTI_GPIO_PORT 'I'
#elif defined(CONFIG_ARCH_MCU_STM32F401)
# define MAX_EXTI_GPIO_PORT 'H'
#else
# error "unsupported SoC EXTI configuration"
#endif

/**
 * @info exti CR field is an incremental value started at 0 (GPIO PA).
 * This allows us to directly use the GPIO port name as base value
 * with the basic algorithm (gpio_port_name - 'A')
 *
 *   EXTI_TARGET_PA = 0b0000,
 *   EXTI_TARGET_PB = 0b0001,
 *   EXTI_TARGET_PC = 0b0010,
 *   EXTI_TARGET_PD = 0b0011,
 *   EXTI_TARGET_PE = 0b0100,
 *   EXTI_TARGET_PF = 0b0101,
 *   EXTI_TARGET_PG = 0b0110,
 *   EXTI_TARGET_PH = 0b0111,
 *   EXTI_TARGET_PI = 0b1000,
 *   EXTI_TARGET_PJ = 0b1001,
 */

static inline kstatus_t syscfg_map(void)
{
    stm32_syscfg_desc_t const * desc = stm32_syscfg_get_desc();
    return mgr_mm_map_kdev(desc->base_addr, desc->size);
}
/* for simplicity sake, but unmaping a kernel device is generic */
static inline kstatus_t syscfg_unmap(void) {
    return mgr_mm_unmap_kdev();
}

#ifdef CONFIG_HAS_FLASH_DUAL_BANK
/**
 * @brief flip the current flash bank that is mapped at address 0x0
 */
kstatus_t syscfg_switch_bank(void)
{
    kstatus_t status;
    if (unlikely((status = syscfg_map()) != K_STATUS_OKAY)) {
        goto err;
    }
    uint32_t reg = ioread32(SYSCFG_BASE_ADDR + SYSCFG_MEMRM_REG);
    /* flipping FB_MODE bit */
    reg ^= SYSCFG_MEMRM_FB_MODE;
    iowrite(SYSCFG_BASE_ADDR + SYSCFG_MEMRM_REG, reg);
    syscfg_unmap();
err:
    return status;
}
#endif

kstatus_t syscfg_probe(void)
{
    kstatus_t status = K_STATUS_OKAY;
    if (unlikely((status = syscfg_map()) != K_STATUS_OKAY)) {
        goto err;
    }
    uint32_t reg = ioread32(SYSCFG_BASE_ADDR + SYSCFG_MEMRM_REG);
#ifdef CONFIG_HAS_FLASH_DUAL_BANK
    /* preserve currently selected bank */
    reg &= SYSCFG_MEMRM_FB_MODE;
#endif
    iowrite(SYSCFG_BASE_ADDR + SYSCFG_MEMRM_REG, 0UL);
    iowrite(SYSCFG_BASE_ADDR + SYSCFG_PMC_REG, 0UL);
    iowrite(SYSCFG_BASE_ADDR + SYSCFG_EXTICR1_REG, 0UL);
    iowrite(SYSCFG_BASE_ADDR + SYSCFG_EXTICR2_REG, 0UL);
    iowrite(SYSCFG_BASE_ADDR + SYSCFG_EXTICR3_REG, 0UL);
    iowrite(SYSCFG_BASE_ADDR + SYSCFG_EXTICR4_REG, 0UL);
    iowrite(SYSCFG_BASE_ADDR + SYSCFG_CMPCR_REG, 0UL);
    syscfg_unmap();
err:
    return status;
}

kstatus_t syscfg_set_exti(uint8_t gpio_pin_id,  uint8_t gpio_port_id)
{
    kstatus_t status = K_STATUS_OKAY;
    if (unlikely(gpio_port_id > MAX_EXTI_GPIO_PORT)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    if (unlikely(gpio_pin_id > 15)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    if (unlikely((status = syscfg_map()) != K_STATUS_OKAY)) {
        goto err;
    }
    size_t exticr = (SYSCFG_BASE_ADDR + SYSCFG_EXTICR1_REG);
    /* selecting the correct EXTICR register (4 exti per register)*/
    exticr += 4*(gpio_pin_id >> 2);
    uint32_t exticr_val = ioread32(exticr);
    /* selecting the correct mask. 4 bits per field */
    uint32_t exticr_shift = (gpio_pin_id % 4)*4;
    /* let's now set the corresponding value */
    exticr = gpio_port_id << exticr_shift;
    iowrite32(SYSCFG_BASE_ADDR + SYSCFG_EXTICR1_REG, exticr_val);
    syscfg_unmap();
err:
    return status;
}
