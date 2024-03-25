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

stack_frame_t *gate_exit(const stack_frame_t *frame, uint32_t result);

stack_frame_t *gate_get_prochandle(stack_frame_t *frame, uint32_t job_label);

stack_frame_t *gate_yield(stack_frame_t *frame);

stack_frame_t *gate_sleep(stack_frame_t *frame, uint32_t duration_ms, uint32_t sleep_mode);

stack_frame_t *gate_start(stack_frame_t *frame, uint32_t target_label);

stack_frame_t *gate_get_random(stack_frame_t *frame);

stack_frame_t *gate_pm_manage(stack_frame_t *frame, uint32_t pm_command);

stack_frame_t *gate_pm_clock_set(stack_frame_t *frame, uint32_t clk_reg, uint32_t clockid, uint32_t val);

stack_frame_t *gate_alarm(stack_frame_t *frame, uint32_t delay_ms);

stack_frame_t *gate_get_cycle(stack_frame_t *frame, uint32_t precision);

stack_frame_t *gate_log(stack_frame_t *frame, [[maybe_unused]] uint32_t log_len);

#endif/*!SYSCALLS_H*/
