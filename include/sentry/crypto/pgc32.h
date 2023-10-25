// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef PGC32_H
#define PGC32_H

#include <stdint.h>

void pcg32_seed(uint64_t seed_state, uint64_t seed_sequence);

uint32_t pcg32(void);

#endif/*!PGC32_H*/
