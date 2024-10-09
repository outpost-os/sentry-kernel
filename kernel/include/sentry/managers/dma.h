// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef SENTRY_MANAGERS_DMA_H
#define SENTRY_MANAGERS_DMA_H

#include <inttypes.h>
#include <uapi/handle.h>
#include <uapi/dma.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/dma/gpdma.h>

#ifdef __cplusplus
extern "C" {
#endif

#if CONFIG_HAS_GPDMA

__STATIC_FORCEINLINE bool mgr_dma_is_irq_owned(int IRQn) {
    bool dma_owned = false;
#ifdef CONFIG_HAS_GPDMA
    dma_owned = gpdma_irq_is_dma_owned(IRQn);
#endif
return dma_owned;
}

kstatus_t mgr_dma_init(void);


kstatus_t mgr_dma_watchdog(void);

kstatus_t mgr_dma_get_owner(dmah_t d, taskh_t *owner);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_dma_autotest(void);
#endif

kstatus_t mgr_dma_get_handle(uint32_t label, dmah_t * handle);

kstatus_t mgr_dma_get_dmah_from_interrupt(uint16_t IRQn, dmah_t *dmah);

kstatus_t mgr_dma_get_state(dmah_t d, gpdma_chan_state_t *state);

kstatus_t mgr_dma_get_info(const dmah_t dmah, gpdma_stream_cfg_t const ** infos);

kstatus_t mgr_dma_stream_assign(const dmah_t dmah);

kstatus_t mgr_dma_stream_unassign(const dmah_t dmah);

kstatus_t mgr_dma_stream_start(const dmah_t dmah);

kstatus_t mgr_dma_stream_stop(const dmah_t dmah);

#endif/* HAS_GPDMA */


#ifdef __cplusplus
} /* extern "C" */
#endif

#endif/*SENTRY_MANAGERS_DMA_H*/
