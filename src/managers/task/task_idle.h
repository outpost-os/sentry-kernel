// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef TASK_IDLE_H
#define TASK_IDLE_H

#include <inttypes.h>
#include <sentry/thread.h>
#include <sentry/managers/task.h>

task_meta_t *task_idle_get_meta(void);

#endif/*!TASK_IDLE_H*/
