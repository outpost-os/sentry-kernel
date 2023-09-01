// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef SYSTICK_H_
#define SYSTICK_H_

#include <inttypes.h>

#include <thread.h>
#include <arch/asm-cortex-m/system.h>


/* FIXME to set*/
#define CONFIG_SYSTICK_HZ 1000


//#include "handler.h"

/*** System timer registers ***/
/* (RW Privileged)  SysTick control and status register (STK_CTRL) */
#define r_CORTEX_M_STK_CTRL	    REG_ADDR(SYSTICK_BASE + 0x00u)
/* (RW Privileged)  SysTick reload value register (STK_LOAD) */
#define r_CORTEX_M_STK_LOAD	    REG_ADDR(SYSTICK_BASE + 0x04u)
/* (RW Privileged)  SysTick current value register (STK_VAL) */
#define r_CORTEX_M_STK_VAL	    REG_ADDR(SYSTICK_BASE + 0x08u)
/* (RO Privileged)  SysTick calibration value register (STK_CALIB) */
#define r_CORTEX_M_STK_CALIB	REG_ADDR(SYSTICK_BASE + 0x0Cu)


/*** SysTick control and status register (STK_CTRL) ***/
/* Bit 16 COUNTFLAG: Returns 1 if timer counted to 0 since last time this was
 * read.
 */
#define STK_COUNTFLAG_Pos	16u
#define STK_COUNTFLAG_Msk	(0x01u << STK_COUNTFLAG_Pos)
/* Bit 2 CLKSOURCE: Clock source selection*/
#define STK_CLKSOURCE_Pos	2u
#define STK_CLKSOURCE_Msk	(0x01u << STK_CLKSOURCE_Pos)
/* Bit 1 TICKINT: SysTick exception request enable*/
#define STK_TICKINT_Pos	1u
#define STK_TICKINT_Msk	(0x01u << STK_TICKINT_Pos)
/* Bit 0 ENABLE: Counter enable*/
#define STK_ENABLE_Pos		0u
#define STK_ENABLE_Msk		(0x01u << STK_ENABLE_Pos)

/*** SysTick reload value register (STK_LOAD) ***/
/* Bits 23:0 RELOAD: RELOAD value The LOAD register specifies the start value
 * to load into the STK_VAL register when the counter is enabled and when it
 * reaches 0.
 */
#define STK_RELOAD_Pos		0u
#define STK_RELOAD_Msk		(0xffffffu << STK_RELOAD_Pos)

/*** SysTick current value register (STK_VAL) ***/
/*  Bits 23:0 CURRENT: Current counter value. The VAL register contains the
 *  current value of the SysTick counter. Reads return the current value of the
 *  SysTick counter. A write of any value clears the field to 0, and also
 *  clears the COUNTFLAG bit in the STK_CTRL register to 0.
 */
#define STK_CURRENT_Pos	0u
#define STK_CURRENT_Msk	(0xffffffu << STK_CURRENT_Pos)

/*** SysTick calibration value register (STK_CALIB) ***/
/* Bit 31 NOREF: NOREF flag. Reads as zero. Indicates that a separate reference
 * clock is provided. The frequency of this clock is HCLK/8.
 */
#define STK_NOREF_Pos		31u
#define STK_NOREF_Msk		(0x01u << STK_NOREF_Pos)
/* Bit 30 SKEW: SKEW flag: Indicates whether the TENMS value is exact. Reads as
 * one. Calibration value for the 1 ms inexact timing is not known because
 * TENMS is not known. This can affect the suitability of SysTick as a software
 * real time clock.
 */
#define STK_SKEW_Pos		30u
#define STK_SKEW_Msk		(0x01u << STK_SKEW_Pos)
/* Bits 23:0 TENMS[23:0]: Calibration value. Indicates the calibration value
 * when the SysTick counter runs on HCLK max/8 as external clock. The value is
 * product dependent, please refer to the Product Reference Manual, SysTick
 * Calibration Value section. When HCLK is programmed at the maximum frequency,
 * the SysTick period is 1ms. If calibration information is not known,
 * calculate the calibration value required from the frequency of the processor
 * clock or external clock.
 */
#define STK_TENMS_Pos		0u
#define STK_TENMS_Msk		(0xffffffu << STK_TENMS_Pos)

#define JIFFIES_TO_SEC(x)  ((x) / CONFIG_SYSTICK_HZ)
#define JIFFIES_TO_MSEC(x) ((x) * 1000UL / CONFIG_SYSTICK_HZ)
#define SEC_TO_JIFFIES(x)  ((x) * CONFIG_SYSTICK_HZ)
#define MSEC_TO_JIFFIES(x) ((x) * CONFIG_SYSTICK_HZ / 1000UL)

typedef uint64_t jiffies_t;

jiffies_t systime_get_jiffies(void);

__attribute__((always_inline))
static inline uint64_t systime_get_seconds(void)
{
    return JIFFIES_TO_SEC(systime_get_jiffies());
}

__attribute__((always_inline))
static inline uint64_t systime_get_milliseconds(void)
{
    return JIFFIES_TO_MSEC(systime_get_jiffies());
}

void systick_init(void);
stack_frame_t *systick_handler(stack_frame_t * stack_frame);
void wait(unsigned long long time_ms);



#endif /* SYSTICK_H_*/
