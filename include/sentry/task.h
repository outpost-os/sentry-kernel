// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef TASK_H
#define TASK_H

#include <inttypes.h>
/**
 * \file sentry kernel generic types
 */

typedef struct task {
    size_t entrypoint;
    uint32_t identifier;
    uint8_t priority;
    /* TODO: add all arch-generic content here */
} task_t;

#endif/*TASK_H*/
