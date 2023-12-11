// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager init automaton functions
 */
#include <inttypes.h>
#include <uapi/uapi.h>

void __attribute__((noreturn)) autotest(void)
{
    bool test_finished = false;
    do {
        /* Let's test */
    } while (!test_finished);
   sys_exit(0);
   do {} while (1);
   __builtin_unreachable();
}
