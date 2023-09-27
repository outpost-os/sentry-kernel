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
#include <sentry/io.h>
#include <sentry/bits.h>
#include <sentry/ktypes.h>
#include <sentry/crypto/crc32.h>
#include "syscfg_defs.h"

#ifdef CONFIG_HAS_FLASH_DUAL_BANK
/**
 * @brief flip the current flash bank that is mapped at address 0x0
 */
void syscfg_switch_bank(void)
{
    uint32_t reg = ioread32(SYSCFG_BASE_ADDR + SYSCFG_MEMRM_REG);
    /* flipping FB_MODE bit */
    reg ^= SYSCFG_MEMRM_FB_MODE;
    iowrite(SYSCFG_BASE_ADDR + SYSCFG_MEMRM_REG, reg);
}
#endif

kstatus_t syscfg_probe(void)
{
    kstatus_t status = K_STATUS_OKAY;
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

    return status;
}

#if 0
// FIXME: need handle definition
kstatus_t syscfg_set_exti(uint8_t exti_pin_id,  gpio_port_id)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t exticr = (SYSCFG_BASE_ADDR + SYSCFG_EXTICR1_REG);
    /* sanitation */
    if (exti_id > 15) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    exticr += 4*(exti_id >> 2);
err:
    return status;
}
#endif
