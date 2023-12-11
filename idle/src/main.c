// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <string.h>

extern size_t _s_idle_svcexchange;
/**
 * @file Sentry task manager init automaton functions
 */
#include <inttypes.h>
#include <uapi/uapi.h>

void __attribute__((noreturn)) idle(void)
{
    const char *welcommsg="hello this is idle!\n";
    memcpy(&_s_idle_svcexchange, welcommsg, 20);
    sys_log(20);

    #if 1
    /* TODO: yield() first, to force task scheduling */
    sys_yield();

    do {
        /* entering LP mode */
        //sys_manage_cpu_sleep(CPU_SLEEP_WAIT_FOR_INTERRUPT);
        /* rise from LP, force task election */
        sys_yield();
    } while (1);
    #else
    do {
        asm volatile("nop");
    } while (1);
    #endif
}
