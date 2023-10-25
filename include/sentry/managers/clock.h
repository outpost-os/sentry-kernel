// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef CLOCK_MANAGER_H
#define CLOCK_MANAGER_H

#ifdef __cplusplus
extern "C" {
#endif
/**
 * @file Sentry Clock manager
 */
#include <sentry/ktypes.h>

kstatus_t mgr_clock_init(void);

#ifdef __cplusplus
}
#endif

#endif/*!CLOCK_MANAGER_H*/
