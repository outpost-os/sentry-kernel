// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef SENTRY_MANAGERS_DMA_H
#define SENTRY_MANAGERS_DMA_H

#include <inttypes.h>
#include <uapi/device.h>
#include <uapi/handle.h>
#include <sentry/ktypes.h>
#include <bsp/drivers/dma/gpdma.h>

#ifdef __cplusplus
extern "C" {
#endif

__STATIC_FORCEINLINE bool mgr_dma_is_irq_owned(int IRQn) {
    return gpdma_irq_is_dma_owned(IRQn);
}

kstatus_t mgr_dma_init(void);

kstatus_t mgr_dma_watchdog(void);

kstatus_t mgr_dma_get_owner(dmah_t d, taskh_t *owner);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_dma_autotest(void);
#endif

kstatus_t mgr_device_get_dmah_from_interrupt(uint16_t IRQn, dmah_t *dmah);

/**
 * Iterate over the device list, starting with id==id.
 * Return the devinfo of the current id increment, or set devinfo to NULL and return K_ERROR_NOENT if
 * the dev list walk is terminated
 */
//kstatus_t mgr_dma_walk(const devinfo_t **devinfo, uint8_t id);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif/*SENTRY_MANAGERS_DMA_H*/
