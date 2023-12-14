// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager init automaton functions
 */
#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <uapi/uapi.h>

extern size_t _s_autotest_svcexchange;

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

void __attribute__((noreturn)) autotest(void)
{
    bool test_finished = false;
    const char *welcommsg="hello this is autotest!\n";
    const char *testmsg="starting test suite...\n";
    uint32_t sleep_time = 1000UL;
    uint32_t count = 0;
    printf(welcommsg);
    printf(testmsg);
    printf("executing loop of %lu ms\n", sleep_time);
    do {
        printf("executing loop %lu\n", count++);
        SleepDuration duration;
        duration.tag = SLEEP_DURATION_ARBITRARY_MS;
        duration.arbitrary_ms = sleep_time;
        sys_sleep(duration, SLEEP_MODE_DEEP);
        /* Let's test */
    } while (!test_finished);
   //sys_exit(0);
   do {asm volatile("nop");} while (1);
   __builtin_unreachable();
}
