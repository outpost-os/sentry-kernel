#ifndef SYSCALLS_H
#define SYSCALLS_H

#include <uapi/handle.h>
#include <sentry/arch/asm-generic/thread.h>

stack_frame_t *gate_send_ipc(stack_frame_t *frame, taskh_t target, uint32_t len);

stack_frame_t *gate_waitforevent(stack_frame_t *frame, uint8_t mask, uint32_t timeout);

stack_frame_t *gate_send_signal(stack_frame_t *frame, taskh_t target, uint32_t signal);

#endif/*!SYSCALLS_H*/
