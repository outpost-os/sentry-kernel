// SPDX-FileCopyrightText: 2024 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef UAPI_DMA_H
#define UAPI_DMA_H

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

#include <assert.h>
#include <inttypes.h>
#include <stddef.h>
#include <stdbool.h>


/**
 * @file DMA-related types declaration
 *
 * In order to properly parse various infos the kernel can deliver to user-space
 * this header declare various types that are DMA related. These types are
 * used by both kernel and userspace in order to avoid any divergence.
 *
*/

/**
 * @enum gpdma_chan_trigger
 *
 * @brief type of DMA tranfer triggers request. This enum is made for bitfield manipulation,
 * allowing multitple triggers at the same time if needed.
 */
typedef enum gpdma_chan_int {
    GPDMA_INT_TC                    = 1, /**< DMA channel trigger on transfer complete */
    GPDMA_INT_HT                    = 2, /**< DMA channel trigger on half transfer and transfer complete */
    GPDMA_INT_ERROR                 = 4, /**< triggers on DMA transfer or config error, get status for complete information */
} gpdma_chan_int_t;

/**
 * @brief generic DMA streams and channel status
 *
 * list DMA-generic status types that can be used by upper layer,
 * whatever the DMA controller and driver is.
 */
typedef struct __attribute__((packed)) gpdma_chan_status {
    uint32_t state: 4;
    uint32_t half_reached: 1;
    uint32_t completed: 1;
    uint32_t reserved: 2;
} gpdma_chan_status_t;

static_assert(sizeof(gpdma_chan_status_t) == sizeof(uint8_t), "O,vamod gpdma_chan_status_t size");

/**
 * @enum gpdma_transfer_type
 *
 * @brief possible DMA transfer types
 */
typedef enum gpdma_transfer_type {
    GPDMA_TRANSFER_MEMORY_TO_DEVICE = 0,
    GPDMA_TRANSFER_DEVICE_TO_MEMORY = 1,
    GPDMA_TRANSFER_MEMORY_TO_MEMORY = 2,
    GPDMA_TRANSFER_DEVICE_TO_DEVICE = 3,
} gpdma_transfer_type_t;

/**
 * @enum gpdma_transfer_mode
 *
 * @brief possible DMA transfer mode
 *
 * This enumerate behaves as a bitfield, allowing multiple values to be set
 * at the same time.
 */
typedef enum gpdma_transfer_mode {
    GPDMA_TRANSFER_MODE_INCREMENT_NONE = 0, /**< no increment at all of src and dest */
    GPDMA_TRANSFER_MODE_INCREMENT_SRC  = 1, /**< increment src at each burst */
    GPDMA_TRANSFER_MODE_INCREMENT_DEST = 2, /**< increment dest at each burst */
} gpdma_transfer_mode_t;

/**
 * @enum gpdma_beat_len
 *
 * @brief possible DMA single manipulation data len (denoted beat)
 * the beat len, associated to the transfer mode and the burst number defined how the
 * DMA behaves.
 *
 * This defines the way burst works and impact the increment calculation. This
 * is defined for both source and dest and may differ, allowing differenciated increment
 */
typedef enum gpdma_beat_len {
    GPDMA_BEAT_LEN_BYTE = 0,     /**< data len to manipulate is a byte */
    GPDMA_BEAT_LEN_HALFWORD = 1, /**< data len to manipulate is a half word */
    GPDMA_BEAT_LEN_WORD = 2,     /**< data len to manipulate is a word */
} gpdma_beat_len_t;

/**
 * @enum gpdma_priority
 *
 * @brief DMA stream priority in comparison with others
 */
typedef enum gpdma_priority {
    GPDMA_PRIORITY_LOW    = 0,
    GPDMA_PRIORITY_MEDIUM = 1,
    GPDMA_PRIORITY_HIGH = 2,
    GPDMA_PRIORITY_VERY_HIGH = 3,
} gpdma_priority_t;

/**
 * @struct gpdma_stream_cfg
 *
 * @brief DMA transfer definition
 *
 * Depending on the hardware, the notion of channels and stream may vary,
 * as sometime the controller hold stream with various channels configuration,
 * or hold channels with various stream (request type) configuration.
 *
 * In order to avoid any difficulties at upper layer:
 * - a channel is always denoted 'channel'
 * - a stream can be a request
 * This couple is always defined in the device-tree file, so that it
 * properly identify a configuration, meaning that the DMA controller
 * configuration is correctly shared between requester at configure time.
 *
 * This means that whatever the driver is, the correct selection of a working
 * stream/channel configuration is fixed and is not automatically detected at
 * run time.
 */
typedef struct gpdma_stream_cfg {
    uint16_t  channel;       /**< channel identifier */
    uint16_t  stream;        /**< request identifier */
    uint16_t  controller;    /**< controller identifier */
    uint16_t  transfer_type; /**< type of transfer, @see gpdma_transfer_type */
    size_t    source;        /**< source address, for memory-to-x requests */
    size_t    dest;          /**< destination address, for x-to-memory requests */
    size_t    transfer_len;  /**< overall steam transfer length in bytes */
    bool      circular_source; /**< make DMA stream restart from initial source addr at trigger time */
    bool      circular_dest; /**< make DMA stream restart from initial dest addr at trigger time */
    uint8_t   interrupts;    /**< interrupt requested, @see gpdma_chan_int */
    bool      is_triggered;  /**< specify if the DMA stream is triggered or not */
    uint8_t   trigger;       /**< trigger id that (re)arm DMA data transfer */
    uint8_t   priority;      /**< DMA stream priority in comparison with others, @see gpdma_priority */
    uint8_t   transfer_mode; /**< DMA transfer mode, @see gpdma_transfer_mode*/
    uint8_t   src_beat_len;  /**< source burst length @see gpdma_beat_len */
    uint8_t   dest_beat_len; /**< source burst length @see gpdma_beat_len */
} gpdma_stream_cfg_t;

/**
 * @brief generic state value definition for a DMA stream, used to get back DMA statuses
 */
typedef enum dma_chan_state {
    GPDMA_STATE_IDLE                    = 1, /**< DMA channel idle (not set or unused) */
    GPDMA_STATE_RUNNING                 = 2, /**< DMA channel is running */
    GPDMA_STATE_ABORTED                 = 3, /**< DMA stream aborted on SW request */
    GPDMA_STATE_SUSPENDED               = 4, /**< DMA stream suspended on SW request*/
    GPDMA_STATE_TRANSMISSION_FAILURE    = 5, /**< DMA transmission failure */
    GPDMA_STATE_CONFIGURATION_FAILURE   = 6, /**< DMA channel configuration failure */
    GPDMA_STATE_OVERRUN                 = 7, /**< DMA transmission overrun */
    GPDMA_STATE_TRANSFER_COMPLETE       = 8, /**< DMA transfer complete for this channel */
    GPDMA_STATE_HALF_TRANSFER           = 9, /**< DMA transfer half-complete for this channel */
} gpdma_chan_state_t;

#ifdef __cplusplus
} /* extern "C" */
#endif // __cplusplus


#endif/*UAPI_DMA_H*/
