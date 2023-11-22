// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager init automaton functions
 */
#include <inttypes.h>
#include <uapi/uapi.h>

void __attribute__((noreturn)) idle(void)
{
    /* TODO: yield() first, to force task scheduling */
    sys_yield();

    do {
        /* entering LP mode */
        sys_manage_cpu_sleep(CPU_SLEEP_WAIT_FOR_INTERRUPT);
        /* rise from LP, force task election */
        sys_yield();
    } while (1);
}
