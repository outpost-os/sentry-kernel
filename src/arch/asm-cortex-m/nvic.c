// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>

#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/arch/asm-cortex-m/nvic.h>
#include <sentry/arch/asm-cortex-m/scb.h>
#include <sentry/arch/asm-generic/membarriers.h>

/**
 * \file NVIC manipulation primitives implementation with hardened support
 * (store, load and check)
 */



 /*
 * NVIC register block is 0xE000E100. The NVIC_STIR register is
 * located in a separate block at 0xE000EF00.
 *
 * The NVIC supports:
 * • Up to 160 interrupts on IMX8MP CM7
 * • A programmable priority level of 0-15 for each interrupt.
 *   A higher level corresponds to a lower priority, so level 0
 *   is the highest interrupt priority
 *
 * • Level and pulse detection of interrupt signals
 *
 * • Dynamic reprioritization of interrupts
 *
 * • Grouping of priority values into group priority and subpriority
 *   fields
 *
 * • Interrupt tail-chaining
 *
 * • An external Non-maskable interrupt (NMI)
 *
 * The processor automatically stacks its state on exception entry and
 * unstacks this state on exception exit, with no instruction overhead.
 */


/* 0xE000E100-0xE000E10B NVIC_ISER0-NVIC_ISER2 (RW Privileged) Interrupt set-enable registers */
#define r_CORTEX_M_NVIC_ISER0   REG_ADDR(NVIC_BASE + 0x00u)
#define r_CORTEX_M_NVIC_ISER1   REG_ADDR(NVIC_BASE + 0x04u)
#define r_CORTEX_M_NVIC_ISER2   REG_ADDR(NVIC_BASE + 0x08u)
/* 0XE000E180-0xE000E18B NVIC_ICER0-NVIC_ICER2 (RW Privileged) Interrupt clear-enable registers */
#define r_CORTEX_M_NVIC_ICER0   REG_ADDR(NVIC_BASE + 0x80u)
#define r_CORTEX_M_NVIC_ICER1   REG_ADDR(NVIC_BASE + 0x84u)
#define r_CORTEX_M_NVIC_ICER2   REG_ADDR(NVIC_BASE + 0x88u)
/* 0XE000E200-0xE000E20B NVIC_ISPR0-NVIC_ISPR2 (RW Privileged) Interrupt set-pending registers */
#define r_CORTEX_M_NVIC_ISPR0   REG_ADDR(NVIC_BASE + 0x100u)
#define r_CORTEX_M_NVIC_ISPR1   REG_ADDR(NVIC_BASE + 0x104u)
#define r_CORTEX_M_NVIC_ISPR2   REG_ADDR(NVIC_BASE + 0x108u)
/* 0XE000E280-0xE000E29C NVIC_ICPR0-NVIC_ICPR2 (RW Privileged) Interrupt clear-pending registers */
#define r_CORTEX_M_NVIC_ICPR0   REG_ADDR(NVIC_BASE + 0x180u)
#define r_CORTEX_M_NVIC_ICPR1   REG_ADDR(NVIC_BASE + 0x184u)
#define r_CORTEX_M_NVIC_ICPR2   REG_ADDR(NVIC_BASE + 0x188u)
/* 0xE000E300-0xE000E31C NVIC_IABR0-NVIC_IABR2 (RW Privileged) Interrupt active bit registers */
#define r_CORTEX_M_NVIC_IABR0   REG_ADDR(NVIC_BASE + 0x200u)
#define r_CORTEX_M_NVIC_IABR1   REG_ADDR(NVIC_BASE + 0x204u)
#define r_CORTEX_M_NVIC_IABR2   REG_ADDR(NVIC_BASE + 0x208u)
/* 0xE000E400-0xE000E503 NVIC_IPR0-NVIC_IPR20  (RW Privileged)Interrupt priority registers */
#define r_CORTEX_M_NVIC_IPR0    REG_ADDR(NVIC_BASE + 0x300u)
#define r_CORTEX_M_NVIC_IPR1    REG_ADDR(NVIC_BASE + 0x301u)
#define r_CORTEX_M_NVIC_IPR2    REG_ADDR(NVIC_BASE + 0x302u)
#define r_CORTEX_M_NVIC_IPR3    REG_ADDR(NVIC_BASE + 0x303u)
#define r_CORTEX_M_NVIC_IPR4    REG_ADDR(NVIC_BASE + 0x304u)
#define r_CORTEX_M_NVIC_IPR5    REG_ADDR(NVIC_BASE + 0x305u)
#define r_CORTEX_M_NVIC_IPR6    REG_ADDR(NVIC_BASE + 0x306u)
#define r_CORTEX_M_NVIC_IPR7    REG_ADDR(NVIC_BASE + 0x307u)
#define r_CORTEX_M_NVIC_IPR8    REG_ADDR(NVIC_BASE + 0x308u)
#define r_CORTEX_M_NVIC_IPR9    REG_ADDR(NVIC_BASE + 0x309u)
#define r_CORTEX_M_NVIC_IPR10   REG_ADDR(NVIC_BASE + 0x310u)
#define r_CORTEX_M_NVIC_IPR11   REG_ADDR(NVIC_BASE + 0x311u)
#define r_CORTEX_M_NVIC_IPR12   REG_ADDR(NVIC_BASE + 0x312u)
#define r_CORTEX_M_NVIC_IPR13   REG_ADDR(NVIC_BASE + 0x313u)
#define r_CORTEX_M_NVIC_IPR14   REG_ADDR(NVIC_BASE + 0x314u)
#define r_CORTEX_M_NVIC_IPR15   REG_ADDR(NVIC_BASE + 0x315u)
#define r_CORTEX_M_NVIC_IPR16   REG_ADDR(NVIC_BASE + 0x316u)
#define r_CORTEX_M_NVIC_IPR17   REG_ADDR(NVIC_BASE + 0x317u)
#define r_CORTEX_M_NVIC_IPR18   REG_ADDR(NVIC_BASE + 0x318u)
#define r_CORTEX_M_NVIC_IPR19   REG_ADDR(NVIC_BASE + 0x310u)
#define r_CORTEX_M_NVIC_IPR20   REG_ADDR(NVIC_BASE + 0x320u)
#define r_CORTEX_M_NIVIC_STIR   REG_ADDR(NVIC_STIR_BASE)    /* 0xE000EF00 (WO Configurable) Software trigger interrupt register */

/* Interrupt set-enable registers (NVIC_ISERx) */
#define NVIC_ISER_SETENA  REG_ADDR(r_CORTEX_M_NVIC_ISER0)

/* Interrupt clear-enable registers (NVIC_ICERx) */
#define NVIC_ICER  REG_ADDR(r_CORTEX_M_NVIC_ICER0)

/* Interrupt set-pending registers (NVIC_ISPRx) */
#define NVIC_ISPR  REG_ADDR(r_CORTEX_M_NVIC_ISPR0)

/* Interrupt clear-pending registers (NVIC_ICPRx) */
#define NVIC_ICPR  REG_ADDR(r_CORTEX_M_NVIC_ICPR0)

/* Interrupt active bit registers (NVIC_IABRx) */
#define NVIC_IABR  REG_ADDR(r_CORTEX_M_NVIC_IABR0)

/* Interrupt priority registers (NVIC_IPRx) */
#define NVIC_IPR   REG_ADDR(r_CORTEX_M_NVIC_IPR0)

/* Software trigger interrupt register (NVIC_STIR) */
#define NVIC_STIR  REG_ADDR(r_CORTEX_M_NIVIC_STIR)

/* Interrupt set-enable registers */
#define NVIC_ISER   REG_ADDR(r_CORTEX_M_NVIC_ISER0)

/* ##########################   NVIC functions  #################################### */

/* \brief  Set Priority Grouping
 * This function sets the priority grouping field using the required
 * unlock sequence.
 * The parameter PriorityGroup is assigned to the field SCB_AIRCR [10:8] PRIGROUP field.
 * Only values from 0..7 are used.
 * In case of a conflict between priority grouping and available
 * priority bits (__NVIC_PRIO_BITS) the smallest possible priority
 * group is set.
 * \param [in]      PriorityGroup  Priority grouping field
 */
void nvic_set_prioritygrouping(uint32_t PriorityGroup)
{
    uint32_t reg_value;
    uint32_t PriorityGroupTmp = (PriorityGroup & (uint32_t) 0x07);  /* only values 0..7 are used          */

    reg_value = *r_CORTEX_M_SCB_AIRCR;  /* read old register configuration    */
    reg_value &= ~(SCB_AIRCR_VECTKEY_Msk | SCB_AIRCR_PRIGROUP_Msk); /* clear bits to change               */
    /* Insert write key and priority group */
    reg_value =
        (reg_value | ((uint32_t) 0x5FA << SCB_AIRCR_VECTKEY_Pos) |
         (PriorityGroupTmp << 8));
    *r_CORTEX_M_SCB_AIRCR = reg_value;
}

/* \brief  Get Priority Grouping
 * This function gets the priority grouping from NVIC Interrupt Controller.
 * Priority grouping is SCB->AIRCR [10:8] PRIGROUP field.
 * \return                Priority grouping field
 */
uint32_t nvig_get_prioritygrouping(void)
{
    return ((*r_CORTEX_M_SCB_AIRCR & SCB_AIRCR_PRIGROUP_Msk) >> SCB_AIRCR_PRIGROUP_Pos);    /* read priority grouping field */
}

/* \brief  Enable External Interrupt
 * This function enables a device specific interrupt in the NVIC interrupt controller.
 * The interrupt number cannot be a negative value.
 * \param [in]      IRQn  Number of the external interrupt to enable
 */
void nvic_enableirq(uint32_t IRQn)
{
    /*  NVIC->ISER[((uint32_t)(IRQn) >> 5)] = (1 << ((uint32_t)(IRQn) & 0x1F));  enable interrupt */
    NVIC_ISER[(uint32_t) ((int32_t) IRQn) >> 5] =
        (uint32_t) (1 << ((uint32_t) ((int32_t) IRQn) & (uint32_t) 0x1F));
    arch_data_sync_barrier();
    arch_inst_sync_barrier();
}

/* \brief  Disable External Interrupt
 * This function disables a device specific interrupt in the NVIC interrupt controller.
 * The interrupt number cannot be a negative value.
 * \param [in]      IRQn  Number of the external interrupt to disable
 */
void nvic_disableirq(uint32_t IRQn)
{
    NVIC_ICER[((uint32_t) (IRQn) >> 5)] = (uint32_t) (1 << ((uint32_t) (IRQn) & 0x1F)); /* disable interrupt */
}

/* \brief  Get Pending Interrupt
 * This function reads the pending register in the NVIC and returns the pending bit
 * for the specified interrupt.
 * \param [in]      IRQn  Number of the interrupt for get pending
 * \return             0  Interrupt status is not pending
 * \return             1  Interrupt status is pending
 */
uint32_t nvic_get_pendingirq(uint32_t IRQn)
{
    /* Return 1 if pending else 0 */
    return ((uint32_t)
            ((NVIC_ISPR[(uint32_t) (IRQn) >> 5] &
              (uint32_t) (1 << ((uint32_t) (IRQn) & 0x1F))) ? 1 : 0));
}

/* \brief  Set Pending Interrupt
 *
 * This function sets the pending bit for the specified interrupt.
 * The interrupt number cannot be a negative value.
 * \param [in]      IRQn  Number of the interrupt for set pending
 */
void nvic_set_pendingirq(uint32_t IRQn)
{
    NVIC_ISPR[((uint32_t) (IRQn) >> 5)] = (uint32_t) (1 << ((uint32_t) (IRQn) & 0x1F)); /* set interrupt pending */
}

/* \brief  Clear Pending Interrupt
 * This function clears the pending bit for the specified interrupt.
 * The interrupt number cannot be a negative value.
 * \param [in]      IRQn  Number of the interrupt for clear pending
 */
void nvic_clear_pendingirq(uint32_t IRQn)
{
    NVIC_ICPR[((uint32_t) (IRQn) >> 5)] = (uint32_t) (1 << ((uint32_t) (IRQn) & 0x1F)); /* Clear pending interrupt */
}

/* \brief  Get Active Interrupt
 * This function reads the active register in NVIC and returns the active bit.
 * \param [in]      IRQn  Number of the interrupt for get active
 * \return             0  Interrupt status is not active
 * \return             1  Interrupt status is active
 */
uint32_t nvic_get_active(uint32_t IRQn)
{
    /* Return 1 if active else 0 */
    return ((uint32_t)
            ((NVIC_IABR[(uint32_t) (IRQn) >> 5] &
              (uint32_t) (1 << ((uint32_t) (IRQn) & 0x1F))) ? 1 : 0));
}

/* \brief  System Reset
 * This function initiate a system reset request to reset the MCU.
 */
void nvic_systemreset(void)
{
request_data_membarrier();                    /* Ensure all outstanding memory accesses included buffered write are completed before reset */
    *r_CORTEX_M_SCB_AIRCR = ((0x5FA << SCB_AIRCR_VECTKEY_Pos) | (*r_CORTEX_M_SCB_AIRCR & SCB_AIRCR_PRIGROUP_Msk) | SCB_AIRCR_SYSRESETREQ_Msk);  /* Keep priority group unchanged */
request_data_membarrier();                    /* Ensure all outstanding memory accesses included buffered write are completed before reset */
    while (1)
        continue;               /* wait until reset */
}
