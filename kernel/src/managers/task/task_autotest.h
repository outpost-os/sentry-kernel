// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef TASK_AUTOTEST_H
#define TASK_AUTOTEST_H

#include <inttypes.h>
#include <sentry/thread.h>
#include <sentry/managers/task.h>

void task_autotest_init(void);

void __attribute__((noreturn)) autotest(void);

task_meta_t *task_autotest_get_meta(void);

#endif/*!TASK_AUTOTEST_H*/
