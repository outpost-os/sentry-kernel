
// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file Sentry task manager init automaton functions
 */
#include <inttypes.h>
#include <string.h>
#include <sentry/thread.h>
#include <sentry/managers/task.h>
#include "task_core.h"
#include "task_init.h"
#include "task_idle.h"

/**
 * ldscript provided
 */
extern size_t _idle_svcexchange;
extern size_t _sidle;
extern size_t _eidle;

void __attribute__((noreturn,section(".idle"))) idle(void)
{
    /* TODO: yield() first, to force task scheduling */

    do {
#ifndef TEST_MODE
        /* TODO: to replace with a sys_set_sleepmode() syscall */
        #if 0
        asm volatile("wfi");
        # else
        asm volatile("nop");
        #endif
#endif
        /* FIXME: yield to add here */
    } while (1);
}


static task_meta_t idle_meta;

void task_idle_init(void)
{
    memset((void*)&idle_meta, 0x0, sizeof(task_meta_t));
    idle_meta.handle.rerun = 0;
    idle_meta.handle.id = SCHED_IDLE_TASK_LABEL;
    idle_meta.handle.familly = HANDLE_TASKID;
    idle_meta.magic = CONFIG_TASK_MAGIC_VALUE;
    idle_meta.flags = (THREAD_FLAG_AUTOSTART|THREAD_FLAG_PANICONEXIT);
    idle_meta.s_text = (size_t)&_sidle;
    idle_meta.text_size = ((size_t)&_eidle - (size_t)&_sidle);
    idle_meta.rodata_size = 0UL;
    idle_meta.data_size = 0UL;
    idle_meta.bss_size = 0UL;
    idle_meta.heap_size = 0UL;
    idle_meta.s_svcexchange = (size_t)&_idle_svcexchange;
    idle_meta.stack_size = 256; /* should be highly enough */
}

task_meta_t *task_idle_get_meta(void)
{
    return &idle_meta;
}
