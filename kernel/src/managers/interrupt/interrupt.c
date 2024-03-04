// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <uapi/handle.h>
#include <sentry/managers/clock.h>
#include <sentry/ktypes.h>
#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-generic/thread.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/managers/device.h>
#include <sentry/managers/task.h>

#include <bsp/drivers/clk/rcc.h>
#include <bsp/drivers/clk/pwr.h>
#include <bsp/drivers/flash/flash.h>

stack_frame_t *userisr_handler(stack_frame_t *frame, int IRQn)
{
    devh_t dev;
    taskh_t owner;
    /* get the device owning the interrupt */
    if (unlikely(mgr_device_get_devh_from_interrupt(IRQn, &dev) != K_STATUS_OKAY)) {
        /* interrupt with no known device ???? */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    /* get the task owning the device */
    if (unlikely(mgr_device_get_owner(dev, &owner) != K_STATUS_OKAY)) {
        /* user interrupt with no owning task ???? */
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    /* push the inth event into the task input events queue */
    if (unlikely(mgr_task_push_int_event(IRQn, owner) == K_STATUS_OKAY)) {
        /* failed to push IRQ event !!! XXX: what do we do ? */
        panic(PANIC_KERNEL_SHORTER_KBUFFERS_CONFIG);
    }
    return frame;
}

kstatus_t mgr_interrupt_init(void)
{
    /** FIXME: implement init part of interrupt manager */
    interrupt_init(); /** still needed again ? */
    return K_STATUS_OKAY;
}

/**
 * @brief enable IRQ line associated to given IRQ number
 *
 * @param[in] irq IRQ number to enable
 *
 * @return K_ERROR_INVPARAM if irq is invalid on the platform, or K_STATUS_OKAY
 */
kstatus_t mgr_interrupt_enable_irq(uint32_t irq)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(irq >= NUM_IRQS)) {
        goto err;
    }
    interrupt_enable_irq(irq);
    status = K_STATUS_OKAY;
err:
    return status;
}

/**
 * @brief disable IRQ line associated to given IRQ number
 *
 * @param[in] irq IRQ number to disable
 *
 * @return K_ERROR_INVPARAM if irq is invalid on the platform, or K_STATUS_OKAY
 */
kstatus_t mgr_interrupt_disable_irq(uint32_t irq)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(irq >= NUM_IRQS)) {
        goto err;
    }
    interrupt_disable_irq(irq);
    status = K_STATUS_OKAY;
err:
    return status;
}

kstatus_t mgr_interrupt_acknowledge_irq(stack_frame_t *frame, int IRQn)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(interrupt_clear_pendingirq(IRQn)!= K_STATUS_OKAY)) {
        goto end;
    }
    status = K_STATUS_OKAY;
end:
    return status;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_interrupt_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif

/** FIXME: add interrupt manipulation (add user handler, del user handler, etc.) */
