// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file STM32 External interrupts controler driver (see ST RM0090 datasheet)
 */
#include <assert.h>
#include <stdbool.h>
#include <stdatomic.h>

#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/io.h>
#include <sentry/bits.h>
#include <sentry/ktypes.h>
#include "exti_defs.h"

#define MAX_EXTI_INTERRUPT  22
#define MAX_EXTI_EVENT      22

/**
 * @brief probe for EXTI controller
 *
 * EXTI fields are set to their reset value
 *
 * @return K_STATUS_OKAY
 */
/*@
  // assigns all registers
  assigns *(uint32_t*)(EXTI_BASE_ADDR .. EXTI_BASE_ADDR + EXTI_PR_REG);
  ensures \result == K_STATUS_OKAY;
 */
kstatus_t exti_probe(void)
{
    kstatus_t status = K_STATUS_OKAY;
    if (unlikely(ioread32(EXTI_BASE_ADDR + EXTI_PR_REG))) {
        /** FIXME: there is some pending interrupts here, action to define */
        /** INFO: the register read had cleared the pending interrupts */
    }
    iowrite32(EXTI_BASE_ADDR + EXTI_IMR_REG, 0x0UL);
    iowrite32(EXTI_BASE_ADDR + EXTI_EMR_REG, 0x0UL);
    iowrite32(EXTI_BASE_ADDR + EXTI_RTSR_REG, 0x0UL);
    iowrite32(EXTI_BASE_ADDR + EXTI_FTSR_REG, 0x0UL);
    iowrite32(EXTI_BASE_ADDR + EXTI_SWIER_REG, 0x0UL);
    /* clear pending (rc_w1) */
    iowrite32(EXTI_BASE_ADDR + EXTI_PR_REG, 0x7fffffUL);
    return status;
}

/**
 * @brief mask external interrupt itn
 */
/*@
  assigns *(uint32_t*)(EXTI_BASE_ADDR + EXTI_IMR_REG);
  ensures itn > MAX_EXTI_INTERRUPT <==> \result == K_ERROR_INVPARAM;
  ensures itn <= MAX_EXTI_INTERRUPT <==> \result == K_STATUS_OKAY;
 */
kstatus_t exti_mask_interrupt(uint8_t itn)
{
    kstatus_t status = K_STATUS_OKAY;
    if (unlikely(itn > MAX_EXTI_INTERRUPT)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    size_t reg = ioread32(EXTI_BASE_ADDR + EXTI_IMR_REG);
    reg &= ~(1UL << itn);
    iowrite32(EXTI_BASE_ADDR + EXTI_IMR_REG, reg);
err:
    return status;
}

/**
 * @brief unmask external interrupt itn
 */
/*@
  assigns *(uint32_t*)(EXTI_BASE_ADDR + EXTI_IMR_REG);
  ensures itn > MAX_EXTI_INTERRUPT <==> \result == K_ERROR_INVPARAM;
  ensures itn <= MAX_EXTI_INTERRUPT <==> \result == K_STATUS_OKAY;
 */
kstatus_t exti_unmask_interrupt(uint8_t itn)
{
    kstatus_t status = K_STATUS_OKAY;
    if (unlikely(itn > MAX_EXTI_INTERRUPT)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    size_t reg = ioread32(EXTI_BASE_ADDR + EXTI_IMR_REG);
    reg |= (1UL << itn);
    iowrite32(EXTI_BASE_ADDR + EXTI_IMR_REG, reg);
err:
    return status;
}

/**
 * @brief mask external event evn
 */
/*@
  assigns *(uint32_t*)(EXTI_BASE_ADDR + EXTI_EMR_REG);
  ensures evn > MAX_EXTI_EVENT <==> \result == K_ERROR_INVPARAM;
  ensures evn <= MAX_EXTI_EVENT <==> \result == K_STATUS_OKAY;
 */
kstatus_t exti_mask_event(uint8_t evn)
{
    kstatus_t status = K_STATUS_OKAY;
    if (unlikely(evn > MAX_EXTI_EVENT)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    size_t reg = ioread32(EXTI_BASE_ADDR + EXTI_EMR_REG);
    reg &= ~(1UL << evn);
    iowrite32(EXTI_BASE_ADDR + EXTI_EMR_REG, reg);
err:
    return status;
}

/**
 * @brief unmask external event evn
 */
/*@
  assigns *(uint32_t*)(EXTI_BASE_ADDR + EXTI_EMR_REG);
  ensures evn > MAX_EXTI_EVENT <==> \result == K_ERROR_INVPARAM;
  ensures evn <= MAX_EXTI_EVENT <==> \result == K_STATUS_OKAY;
 */
kstatus_t exti_unmask_event(uint8_t evn)
{
    kstatus_t status = K_STATUS_OKAY;
    if (unlikely(evn > MAX_EXTI_EVENT)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    size_t reg = ioread32(EXTI_BASE_ADDR + EXTI_EMR_REG);
    reg |= (1UL << evn);
    iowrite32(EXTI_BASE_ADDR + EXTI_EMR_REG, reg);
err:
    return status;
}

/**
 * @brief generate interrupt identified by itn (software triggered)
 */
/*@
  assigns *(uint32_t*)(EXTI_BASE_ADDR + EXTI_EMR_REG);
  ensures itn > MAX_EXTI_INTERRUPT <==> \result == K_ERROR_INVPARAM;
  ensures itn <= MAX_EXTI_EVENT ==>
      \result == K_STATUS_OKAY || \result == K_ERROR_BADSTATE;
 */
kstatus_t exti_generate_swinterrupt(uint8_t itn)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t reg;
    if (unlikely(itn > MAX_EXTI_INTERRUPT)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    reg = ioread32(EXTI_BASE_ADDR + EXTI_IMR_REG);
    if (unlikely((reg & (0X1UL << itn)) == 0)) {
        /* interrupt is masked */
        status = K_ERROR_BADSTATE;
        goto err;
    }
    reg = ioread32(EXTI_BASE_ADDR + EXTI_SWIER_REG);
    if (unlikely((reg & (0X1UL << itn)))) {
        /* bit already set */
        status = K_ERROR_BADSTATE;
        goto err;
    }
    reg |= (1UL << itn);
    iowrite32(EXTI_BASE_ADDR + EXTI_EMR_REG, reg);
err:
    return status;
}

/**
 * @brief Clear pending interrupt flag for itn
 */
/*@
  assigns *(uint32_t*)(EXTI_BASE_ADDR + EXTI_PR_REG);
  ensures itn > MAX_EXTI_INTERRUPT <==> \result == K_ERROR_INVPARAM;
  ensures itn <= MAX_EXTI_EVENT ==>
      \result == K_STATUS_OKAY;
 */
kstatus_t exti_clear_pending(uint8_t itn)
{
    kstatus_t status = K_STATUS_OKAY;
    if (unlikely(itn > MAX_EXTI_INTERRUPT)) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    /* clear pending (rc_w1) */
    iowrite32(EXTI_BASE_ADDR + EXTI_PR_REG, (0x1UL << itn));
err:
    return status;
}
