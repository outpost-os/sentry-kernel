// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/managers/clock.h>
#include <sentry/ktypes.h>
#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-generic/thread.h>

#include <bsp/drivers/clk/rcc.h>
#include <bsp/drivers/clk/pwr.h>
#include <bsp/drivers/flash/flash.h>

stack_frame_t *userisr_handler(stack_frame_t *frame, int IRQn)
{
    stack_frame_t *next_frame = frame;

    return next_frame;
}

kstatus_t mgr_interrupt_init(void)
{
    /** FIXME: implement init part of interrupt manager */
    interrupt_init(); /** still needed again ? */
    return K_STATUS_OKAY;
}

/** FIXME: add interrupt manipulation (add user handler, del user handler, etc.) */
