// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef BSP_DRIVER_GPDMA_H
#define BSP_DRIVER_GPDMA_H

#ifdef CONFIG_HAS_GPDMA

/**
 * \file General purpose DMA driver generic upper API
 */

#ifdef __cplusplus
#define extern "C" {
#endif

#include <sentry/zlib/compiler.h>
#include <dt-bindings/dma/stm32_dma.h>
#include <uapi/dma.h>

/**
 * @brief generic state value definition for a DMA channel
 *
 * This enumerate aliasing UAPI to keep unified gpdma_ prefixed content at driver level
 * @see dma_chan_state_t definition in uapi/dma.h for corresponding content.
 */

/**
 *  NOTE: the gpdma_stream_cfg_t is a shared data content with user interface
 * the goal is to allow easy user access to stream config through a dedicated syscall,
 * without any manipulation of the device tree.
 * This structure is arch-independent and IP-independent.
 * @see uapi/types.h for the structure definition.
 */

/**
 * @brief probe given GPDMA controller identifier
 */
kstatus_t gpdma_probe(uint8_t controller);

/**
 * @brief clear given channel status flags
 */
kstatus_t gpdma_channel_clear_status(gpdma_stream_cfg_t const*const desc);

/**
 * @brief get back current status of given DMA descriptor's stream
 */
kstatus_t gpdma_channel_get_status(gpdma_stream_cfg_t const*const desc, gpdma_chan_status_t * status);

/**
 * @brief configure a DMA channel with given DMA descriptor
 *
 * @note this function do not enable the DMA channel, but only configure it
 */
kstatus_t gpdma_channel_configure(gpdma_stream_cfg_t const*const desc);

/**
 * @brief enable a previously configured DMA channel
 */
kstatus_t gpdma_channel_enable(gpdma_stream_cfg_t const*const desc);

/**
 * @brief given a stream, get back the associated IRQn
 */
kstatus_t gpdma_get_interrupt(gpdma_stream_cfg_t const * const desc, uint16_t * const IRQn);

/**
 * @brief return true if the IRQn is owned by a DMA controller
 */
bool gpdma_irq_is_dma_owned(uint16_t IRQn);

/**
 * @brief clear interrupt of corresponding stream at GPDMA level
*/
kstatus_t gpdma_interrupt_clear(gpdma_stream_cfg_t const * const desc);

/**
 * @brief suspend currently started stream
 */
kstatus_t gpdma_channel_suspend(gpdma_stream_cfg_t const*const desc);

/**
 * @brief resume previously suspended stream
 */
kstatus_t gpdma_channel_resume(gpdma_stream_cfg_t const*const desc);

/**
 * @brief reset currently suspended stream
 */
kstatus_t gpdma_channel_reset(gpdma_stream_cfg_t const*const desc);

#ifdef __cplusplus
}
#endif

#endif/*!CONFIG_HAS_GPDMA*/

#endif/*!BSP_DRIVER_GPDMA_H*/
