// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager init automaton functions
 */
#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <uapi/uapi.h>
#include <testlib/assert.h>
#include <testlib/core.h>
#include "tests/test_sleep.h"
#include "tests/test_cycles.h"

uint32_t __stack_chk_guard = 0;

/**
 * NOTE: autotest task is a 'bare' Sentry kernel task, meaning that there is
 * no build system calculating each section and mapping the task on the target.
 *
 * As a consequence, the kernel is not able to determine the size of the .data
 * and .bss sections, and these two values are hardcoded (data and bss set to 0)
 * This means that autotest task MUST NOT use any globals.
 *
 * Of course, this restriction do not impact standard userspace apps :-)
 */

void __attribute__((no_stack_protector, used, noreturn)) autotest(uint32_t label, uint32_t seed)
{
    bool test_finished = false;
    /* update SSP value with given seed */
    __stack_chk_guard = seed;
    const char *welcommsg="hello this is autotest!\n";
    const char *testmsg="starting test suite...\n";

    printf(welcommsg);
    printf(testmsg);

    test_cycles();
    test_sleep();

    /* all tests finished, leaving */
    sys_exit(0);
    __builtin_unreachable();
}
