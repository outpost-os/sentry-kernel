// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/ktypes.h>
#include <sentry/managers/task.h>
#include <sentry/managers/dma.h>
#include <sentry/managers/security.h>
#include "dma-dt.h"
#include "dma.h"

static dma_stream_state_t stream_state[STREAM_LIST_SIZE];

#ifndef CONFIG_HAS_GPDMA
static_assert(STREAM_LIST_SIZE, "Can't have streams when no GPDMA supported!");
#endif

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
        uint32_t seed = 0;

        /* Add entropy to handle initialization */
        if (unlikely(mgr_security_entropy_generate(&seed) != K_STATUS_OKAY)) {
            panic(PANIC_HARDWARE_INVALID_STATE);
        }
        kdmah.reserved = seed;

        dmah_t const *dmah = kdmah_to_dmah(&kdmah);
        if (unlikely(dma_stream_get_meta(streamid, &stream_state[streamid].meta) != K_STATUS_OKAY)) {
            panic(PANIC_CONFIGURATION_MISMATCH);
        }
        if (unlikely(mgr_task_get_handle(stream_state[streamid].meta->owner, &stream_state[streamid].owner) != K_STATUS_OKAY)) {
            panic(PANIC_CONFIGURATION_MISMATCH);
        }

        /*@ assert \valid(dmah); */
        /*@ assert \valid_read(stream_state[streamid].meta); */
        stream_state[streamid].handle = *dmah;
        stream_state[streamid].state = DMA_STREAM_STATE_UNSET; /** FIXME: define status types for streams */
    }
#endif
    return status;
}

kstatus_t mgr_dma_watchdog(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}

kstatus_t mgr_dma_get_handle(uint32_t label, dmah_t * handle)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(handle == NULL)) {
        goto end;
    }

#if STREAM_LIST_SIZE
    for (size_t streamid = 0; streamid < STREAM_LIST_SIZE; ++streamid) {
        if (stream_state[streamid].meta->label == label) {
            *handle = stream_state[streamid].handle;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
#endif
end:
    return status;
}

/**
 * @brief given a DMA stream handle, return the task handle associated to it
 *
 * @param[in] dmah: DMA handle for which the owner is asked
 * @param[out] owner: Owner of the DMA handle, if found

 *
 * @return
 *   K_ERROR_INVPARAM: handle does not exist or owner is not valid
 *   K_STATUS_OKAY: owner found and owner argument updated
 */
kstatus_t mgr_dma_get_owner(dmah_t d, taskh_t *owner)
{
    kstatus_t status = K_ERROR_INVPARAM;
    uint32_t owner_label;
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
    *owner = stream_state[kdmah->streamid].owner;
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

/**
 * @brief given an IRQ number, return the started stream's handle associated to it
 *
 * This concept requires that each DMA controler's channel is linked to a single handle at a given time
 *
 * @param[in] IRQn: IRQ number received from the core (nvic, etc.) IRQ controller
 * @param[out] dmah: DMA handle that is associated to that IRQ
 *
 * @return
 *   K_ERROR_INVPARAM: handle is not a valid pointer
 *   K_STATUS_OKAY: stream assignation done with success
 */
kstatus_t mgr_dma_get_dmah_from_interrupt(const uint16_t IRQn, dmah_t *dmah)
{
    kstatus_t status = K_ERROR_INVPARAM;
    if (unlikely(dmah == NULL)) {
        goto end;
    }
    status = K_ERROR_NOENT;
end:
    return status;
}

/**
 * @brief assign a DMA stream configuration associated to given handle to the DMA controller channel
 *
 * The DMA stream is not started, but only assigned. The stream can be started either by a
 * hardware IP configured in DMA mode in case of DEVICE_TO_MEMORY mode, or by a call to the DMA
 * stream start syscall.
 *
 * @param[in] dmah: DMA handle that is boot-time associated to the stream
 *
 * @return
 *   K_ERROR_INVPARAM: handle is not found
 *   K_ERROR_BADSTATE: the stream is already assigned/started
 *   K_STATUS_OKAY: stream assignation done with success
 */
kstatus_t mgr_dma_stream_assign(const dmah_t dmah)
{
    kstatus_t status = K_ERROR_INVPARAM;
end:
    return status;
}

/**
 * @brief unassign a DMA stream configuration associated to given handle from the DMA controller channel
 *
 * The DMA stream is unassigned, the channel is reconfigured to its reset time value.
 *
 * @param[in] dmah: DMA handle that is boot-time associated to the stream
 *
 * @return
 *   K_ERROR_INVPARAM: handle is not found
 *   K_ERROR_BADSTATE: the stream is not assigned or is currently started
 *   K_STATUS_OKAY: stream assignation done with success
 */
kstatus_t mgr_dma_stream_unassign(const dmah_t dmah)
{
    kstatus_t status = K_ERROR_INVPARAM;
end:
    return status;
}

/**
 * @brief update DMA stream dynamic fields
 *
 * @param[in] dmah: DMA stream handle to set
 * @param[in] src_offset: offset (in bytes) starting from source address of DTS stream
 * @param[in] dest_offset: offset (in bytes) starting from destination address of DTS stream
 *
 * @return
 *   K_STATUS_OKAY: offsets are updated. The stream must not be started. If assigned, the channel configuration is updated
 *   K_ERROR_INVPARAM: one of the parameters is invalid
 *   K_ERROR_BADSTATE: stream is started and can't be dynamically updated now.
 */
kstatus_t mgr_dma_update_streamcfg(const dmah_t dmah, size_t src_offset, size_t dest_offset)
{
    kstatus_t status = K_ERROR_INVPARAM;
end:
    return status;
}

/**
 * @brief start a previously assigned DMA stream associated to given handle
 *
 * The DMA stream is started. It is considered that it has been previously assigned.
 *
 * @param[in] dmah: DMA handle that is boot-time associated to the stream
 *
 * @return
 *   K_ERROR_INVPARAM: handle is not found
 *   K_ERROR_BADSTATE: the stream is already started or has not been assigned
 *   K_STATUS_OKAY: stream has been started
 */
kstatus_t mgr_dma_stream_start(const dmah_t dmah)
{
    kstatus_t status = K_ERROR_INVPARAM;
end:
    return status;
}

/**
 * @brief Stop an already started DMA stream identified by dmah
 *
 * @param[in]: dmah: DMA handle that is boot-time associated to the stream
 *
 * @return
 *   K_ERROR_INVPARAM: handle is not found
 *   K_ERROR_BADSTATE: the stream is not started
 *   K_STATUS_OKAY: stream has been stopped
 */
kstatus_t mgr_dma_stream_stop(const dmah_t dmah)
{
    kstatus_t status = K_ERROR_INVPARAM;
end:
    return status;
}
