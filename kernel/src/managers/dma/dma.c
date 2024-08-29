// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/ktypes.h>
#include <sentry/managers/task.h>
#include <sentry/managers/dma.h>
#include "dma-dt.h"
#include "dma.h"

/**
 * @brief Manager level stream configuration
 *
 * This structure associate a hardware DMA stream configuration (dts-based) to
 * the stream owner (also dts-based, using associated channel owner)
 */
typedef struct dma_stream_state {
    dma_meta_t const         * meta; /**< Hardware configuration of the stream */
    dmah_t                     handle; /**< associated DMA handle (opaque format) */
    size_t                     status; /**< TODO: specify stream state enumeration (started, stopped, error...) */
} dma_stream_state_t;


static dma_stream_state_t stream_state[STREAM_LIST_SIZE];

kstatus_t mgr_dma_init(void)
{
    kstatus_t status = K_STATUS_OKAY;

#if STREAM_LIST_SIZE
    for (size_t streamid = 0; streamid < STREAM_LIST_SIZE; ++streamid) {
        kdmah_t kdmah = {
            .reserved = 0,
            .family = HANDLE_DMA,
            .streamid = streamid,
        };
        dmah_t const *dmah = kdmah_to_dmah(&kdmah);
        if (unlikely(dma_stream_get_meta(streamid, &stream_state[streamid].meta) != K_STATUS_OKAY)) {
            panic(PANIC_CONFIGURATION_MISMATCH);
        }
        /*@ assert \valid(dmah); */
        /*@ assert \valid_read(stream_state[streamid].meta); */
        stream_state[streamid].handle = *dmah;
        stream_state[streamid].status = 0; /** FIXME: define status types for streams */
    }
#endif
    return status;
}

kstatus_t mgr_dma_watchdog(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}

kstatus_t mgr_dma_get_owner(dmah_t d, taskh_t *owner)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(owner == NULL)) {
        goto end;
    }
    kdmah_t const *kdmah = dmah_to_kdmah(&d);
    if (kdmah->streamid >= STREAM_LIST_SIZE) {
        goto end;
    }
    if (stream_state[kdmah->streamid].handle != d) {
        goto end;
    }
    *owner = stream_state[kdmah->streamid].meta->owner;
    status = K_STATUS_OKAY;
end:
    return status;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_dma_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif

kstatus_t mgr_dma_get_dmah_from_interrupt(uint16_t IRQn, dmah_t *dmah)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(dmah == NULL)) {
        goto end;
    }
    status = K_ERROR_NOENT;
end:
    return status;
}
