
// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager init automaton functions
 */
#include <inttypes.h>
#include <sentry/thread.h>
#include <sentry/task.h>
#include "task_core.h"
#include "task_init.h"
#include "task_idle.h"

void __attribute__((noreturn,used)) idle(void)
{
    do {
        asm volatile("wfi");
        /* FIXME: yield to add here */
    } while (1);
}


task_meta_t idle_meta;

task_meta_t *task_idle_get_meta(void)
{
    return &idle_meta;
}
