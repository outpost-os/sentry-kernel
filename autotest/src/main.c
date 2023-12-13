// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager init automaton functions
 */
#include <string.h>
#include <inttypes.h>
#include <uapi/uapi.h>

extern size_t _s_autotest_svcexchange;

int foo;
int bla=42;

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
    const char *plop="autoplop!\n";
    foo = 12;
    bla = 14;
    memcpy(&_s_autotest_svcexchange, welcommsg, 24);
    sys_log(24);
    memcpy(&_s_autotest_svcexchange, testmsg, 23);
    sys_log(23);
    do {
        asm volatile("nop");
        memcpy(&_s_autotest_svcexchange, plop, 10);
        sys_log(10);
        /* Let's test */
    } while (!test_finished);
   //sys_exit(0);
   do {asm volatile("nop");} while (1);
   __builtin_unreachable();
}
