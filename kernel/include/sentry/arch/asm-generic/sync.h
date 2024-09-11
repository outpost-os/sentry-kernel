// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef _SYNC_H
#define _SYNC_H

#include <inttypes.h>
#include <stdbool.h>
#include "membarriers.h"


/*
 * Make sure that any explicit data memory transfer specified before is done before the
 * next data memory transfer.
 */

#define semaphore_t uint32_t

bool _semaphore_trylock(volatile uint32_t* semaphore);

bool _semaphore_release(volatile uint32_t* semaphore);

void mutex_init(uint32_t * mutex);

bool mutex_trylock(uint32_t * mutex);

void mutex_lock(uint32_t * mutex);

void mutex_unlock(uint32_t * mutex);

bool mutex_tryunlock(uint32_t * mutex);

#endif
