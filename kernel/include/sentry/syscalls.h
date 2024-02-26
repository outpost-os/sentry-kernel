#ifndef SYSCALLS_H
#define SYSCALLS_H

#include <uapi/handles.h>
#include <sentry/arch/asm-generic/thread.h>

stack_frame_t *gate_send_ipc(stack_frame_t *frame, taskh_t target, uint32_t len);
stack_frame_t *gate_recv_event(stack_frame_t *frame);

#endif/*!SYSCALLS_H*/
