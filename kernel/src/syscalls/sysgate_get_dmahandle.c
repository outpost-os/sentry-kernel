#include <sentry/syscalls.h>
#include <sentry/managers/dma.h>
#include <sentry/sched.h>


stack_frame_t *gate_get_dmahandle(stack_frame_t *frame, uint32_t streamlabel)
{
    taskh_t current = sched_get_current();
#ifdef CONFIG_HAS_GPDMA
    stack_frame_t *next_frame = frame;
    taskh_t owner;
    dmah_t dmahandle;
    const task_meta_t *meta;
    uint32_t *svcexch;

    if (unlikely(mgr_dma_get_handle(streamlabel, &dmahandle) != K_STATUS_OKAY)) {
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_dma_get_owner(dmahandle, &owner) != K_STATUS_OKAY)) {
        /* smoke test here, this branch should never happen */
        /*@ assert(false); */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    if (unlikely(mgr_security_has_capa(current, CAP_DEV_DMA) != SECURE_TRUE)) {
        mgr_task_set_sysreturn(current, STATUS_DENIED);
        goto end;
    }
    if (unlikely(owner != current)) {
        /**
         * INFO: do not declare a different return type on ownership check error to
         * avoid the ability to list all other devices id by sequential calls with
         * DENIED return
         */
        mgr_task_set_sysreturn(current, STATUS_INVALID);
        goto end;
    }
    /* set dmah_t value into svcexchange */
    if (unlikely(mgr_task_get_metadata(current, &meta) != K_STATUS_OKAY)) {
        panic(PANIC_KERNEL_INVALID_MANAGER_RESPONSE);
    }
    svcexch = (uint32_t*)meta->s_svcexchange;
    svcexch[0] = dmahandle;
    mgr_task_set_sysreturn(current, STATUS_OK);
end:
    return next_frame;
#else
    /* no GPDMA support, return no entity status code */
    mgr_task_set_sysreturn(current, STATUS_NO_ENTITY);
    return frame;
#endif
}
