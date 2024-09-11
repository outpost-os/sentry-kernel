// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <sentry/managers/task.h>
#include <sentry/managers/security.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/sched.h>

stack_frame_t *gate_get_random(stack_frame_t *frame)
{
    taskh_t current = sched_get_current();
    stack_frame_t *next_frame = frame;
    uint32_t rngval = 0;
    const task_meta_t *meta;
    uint32_t *svcexch;

    if (unlikely(mgr_security_has_capa(current, CAP_CRY_KRNG) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(mgr_security_entropy_generate(&rngval) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_CRITICAL);
        goto end;
    }
    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    svcexch = (uint32_t*)meta->s_svcexchange;
    svcexch[0] = rngval;
    if (unlikely(mgr_task_set_sysreturn(current, STATUS_OK) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
end:
    return next_frame;
}
