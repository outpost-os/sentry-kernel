// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/syscalls.h>
#include <uapi/types.h>
#include <uapi/dma.h>
#include <sentry/managers/dma.h>
#include <sentry/managers/task.h>
#include <sentry/sched.h>
#include <string.h>

stack_frame_t *gate_dma_start(stack_frame_t *frame, dmah_t dmah)
{
    taskh_t current = sched_get_current();
    Status sysret = STATUS_NO_ENTITY;
#ifdef CONFIG_HAS_GPDMA
    const task_meta_t * meta;
    gpdma_stream_cfg_t const * kinfo = NULL;

    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    if (unlikely(mgr_dma_stream_start(dmah) != K_STATUS_OKAY)) {
        sysret = STATUS_INVALID;
        goto end;
    }
    sysret = STATUS_OK;
end:
#endif
    mgr_task_set_sysreturn(current, sysret);
    return frame;
}
