#ifndef DRIVERS_TIMER_H
#define DRIVERS_TIMER_H

int timer_init(void);

int timer_enable(void);

int timer_release(void);

int timer_enable_interrupt(void);

int timer_disable_interrupt(void);

int timer_interrupt_acknowledge(void);

int timer_restart(void);

Status timer_map(void);

Status timer_unmap(void);

#endif/*! DRIVERS_TIMER_H */
