#ifndef INTERRUPT_MANAGER_H
#define INTERRUPT_MANAGER_H

#ifdef __cplusplus
extern "C" {
#endif
/**
 * @file Sentry Debug manager
 */
#include <sentry/ktypes.h>

/**
 * This is the interrupt handler for IRQ lines associated to ressources that
 * can be declared as userspace ressources (i.e. no exception, no system interrupts)
 */
stack_frame_t *userisr_handler(stack_frame_t *frame, int IRQn);

static inline kstatus_t mgr_interrupt_early_init(void) {
    interrupt_disable();
    interrupt_init();
    return K_STATUS_OKAY;
}

kstatus_t mgr_interrupt_init(void);


#ifdef __cplusplus
}
#endif

#endif/*!INTERRUPT_MANAGER_H*/
