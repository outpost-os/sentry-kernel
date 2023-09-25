// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef RNG_H
#define RNG_H

#include <sentry/ktypes.h>
/**
 * \file RNG hardware kernel source public API. Should be kept the same for
 * any RNG generator driver.
 */

kstatus_t rng_probe(void);

kstatus_t rng_get(uint32_t * random);

#endif/*!RNG_H*/
