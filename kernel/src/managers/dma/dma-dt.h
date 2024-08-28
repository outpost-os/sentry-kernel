// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef DMA_DT_H
#define DMA_DT_H

/**
 * @file Sentry DMA streams access API
 */
#include <inttypes.h>

/**
 * @brief Get owner of given stream
 *
 * Given a stream identifier (), return the corresponding owner
 *
 * @param streamid[in]: streamid field of kdmah_t, part of the dmah_t opaque
 * @param owner[out]: pointer to a taskh_t
 *
 * @returns K_ERROR_INVPARAM if streamid is invalid or owner NULL, or K_STATUS_OKAY
 */
kstatus_t dma_stream_get_owner(size_t streamid, taskh_t const * owner);

/**
 * @brief Get config of given stream
 *
 * Given a stream identifier, return the corresponding stream configuration
 *
 * @param streamid[in]: streamid field of kdmah_t, part of the dmah_t opaque
 * @param owner[out]: pointer to a taskh_t
 *
 * @returns K_ERROR_INVPARAM if streamid is invalid or owner NULL, or K_STATUS_OKAY
 */
kstatus_t dma_stream_get_config(size_t streamid, gpdma_stream_cfg_t const ** cfg);

kstatus_t dma_stream_get_label(size_t streamid, size_t * label);

#endif/*!DMA_DT_H*/
