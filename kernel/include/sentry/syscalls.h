#ifndef SYSCALLS_H
#define SYSCALLS_H

#include <uapi/handle.h>
#include <sentry/arch/asm-generic/thread.h>

stack_frame_t *gate_send_ipc(stack_frame_t *frame, taskh_t target, uint32_t len);

stack_frame_t *gate_waitforevent(stack_frame_t *frame, uint8_t mask, uint32_t timeout);

stack_frame_t *gate_send_signal(stack_frame_t *frame, taskh_t target, uint32_t signal);

stack_frame_t *gate_gpio_set(stack_frame_t *frame, devh_t devhandle, uint8_t io, bool val);

stack_frame_t *gate_gpio_get(stack_frame_t *frame, devh_t devhandle, uint8_t io);

stack_frame_t *gate_gpio_reset(stack_frame_t *frame, devh_t devhandle, uint8_t io);

stack_frame_t *gate_gpio_toggle(stack_frame_t *frame, devh_t devhandle, uint8_t io);

stack_frame_t *gate_gpio_configure(stack_frame_t *frame, devh_t devhandle, uint8_t io);

stack_frame_t *gate_get_devhandle(stack_frame_t *frame, uint8_t devid);

stack_frame_t *gate_int_acknowledge(stack_frame_t *frame, uint16_t IRQn);

stack_frame_t *gate_map_dev(stack_frame_t *frame, devh_t device);

stack_frame_t *gate_unmap_dev(stack_frame_t *frame, devh_t device);

#endif/*!SYSCALLS_H*/