// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef IO_MANAGER_H
#define IO_MANAGER_H

/**
 * @file Sentry I/O manager API
 */

#include <sentry/ktypes.h>
#include <uapi/handle.h>
#include <uapi/device.h>

#ifdef __cplusplus
extern "C" {
#endif

kstatus_t mgr_io_init(void);

kstatus_t mgr_io_set(uint8_t ioport, uint8_t iopin);

kstatus_t mgr_io_reset(uint8_t ioport, uint8_t iopin);

kstatus_t mgr_io_read(uint8_t ioport, uint8_t iopin, bool *val);

kstatus_t mgr_io_configure(io_info_t io);

kstatus_t mgr_io_mask_interrupt(uint8_t ioport, uint8_t iopin);

kstatus_t mgr_io_unmask_interrupt(uint8_t ioport, uint8_t iopin);

kstatus_t mgr_io_mask_event(uint8_t ioport, uint8_t iopin);

kstatus_t mgr_io_unmask_event(uint8_t ioport, uint8_t iopin);

kstatus_t mgr_io_clear_pending_interrupt(uint8_t ioport, uint8_t iopin);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_io_autotest(void);
#endif

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif/*IO_MANAGER_H*/
