// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef IO_MANAGER_H
#define IO_MANAGER_H

/**
 * @file Sentry I/O manager API
 */

#include <sentry/ktypes.h>

kstatus_t io_probe(void);

kstatus_t io_set(ioh_t ioh);

kstatus_t io_reset(ioh_t ioh);

kstatus_t io_read(ioh_t ioh, bool *val);

kstatus_t io_configure(ioh_t ioh);

#endif/*IO_MANAGER_H*/
