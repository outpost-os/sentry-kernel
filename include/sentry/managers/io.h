// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef IO_MANAGER_H
#define IO_MANAGER_H

/**
 * @file Sentry I/O manager API
 */

#include <sentry/ktypes.h>
#include <uapi/handle.h>

kstatus_t mgr_io_probe(void);

kstatus_t mgr_io_set(ioh_t ioh);

kstatus_t mgr_io_reset(ioh_t ioh);

kstatus_t mgr_io_read(ioh_t ioh, bool *val);

kstatus_t mgr_io_configure(ioh_t ioh);

kstatus_t mgr_io_mask_interrupt(ioh_t ioh);

kstatus_t mgr_io_unmask_interrupt(ioh_t ioh);

kstatus_t mgr_io_mask_event(ioh_t ioh);

kstatus_t mgr_io_unmask_event(ioh_t ioh);

kstatus_t mgr_io_clear_pending_interrupt(ioh_t ioh);

#endif/*IO_MANAGER_H*/
