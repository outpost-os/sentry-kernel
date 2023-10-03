// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager
 */

#include <inttypes.h>
#include <sentry/thread.h>
#include <sentry/task.h>

/*
 * Forge a stack context
 */
void initialize_stack_context(size_t sp, size_t pc)
{
    __thread_init_stack_context(sp, pc);
    return;
}
