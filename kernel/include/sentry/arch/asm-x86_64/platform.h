// SPDX-FileCopyrightText: 2023 Ledge SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __PLATFORM_H_
#define __PLATFORM_H_

#ifndef PLATFORM_H
#error "arch specific header must not be included directly!"
#endif

#include <limits.h>
#include <sentry/arch/asm-x86_64/thread.h>
#include <sentry/io.h>

#define THREAD_MODE_USER    0xab2f5332UL
#define THREAD_MODE_KERNEL  0x5371a247UL

/**
 * @def alignment size of sections. 8bytes on x86_64
 */
#define SECTION_ALIGNMENT_LEN 0x8UL

static inline void __attribute__((noreturn)) __platform_spawn_thread(size_t entrypoint __attribute__((unused)),
                                                                     stack_frame_t *stack_pointer  __attribute__((unused)),
                                                                     uint32_t flag __attribute__((unused)))
{
  /* TODO: by now, nothing done in x86_64 test mode. Maybe execv() */
  do { } while (1);
}

static inline void __platform_clear_flags(void) {
    return;
}

void __platform_init(void);


#endif/*!__PLATFORM_H_*/
