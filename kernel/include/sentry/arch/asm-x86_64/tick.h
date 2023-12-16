// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __ASM_TICK_H
#define __ASM_TICK_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stddef.h>
#include <inttypes.h>
#include <time.h>

/* no need for init function on POSIX API */
static inline void systime_init(void) {}

/**
 * @file x86_64 implementation of the ticker
 * cycle counter access is using arch-specific rdtsc assembly code
 * miliseconds and microseconds since bootup is using POSIX clock_gettime() API
 */
__attribute__((always_inline))
static inline uint64_t systime_get_milliseconds(void)
{
    struct timespec spec;
    uint64_t time_ms;
    clock_gettime(CLOCK_MONOTONIC, &spec);
    time_ms = (spec.tv_sec*1000UL) + (spec.tv_nsec / 0x1000000UL);
    return time_ms;
}

__attribute__((always_inline))
static inline uint64_t systime_get_microseconds(void) {
    struct timespec spec;
    uint64_t time_ms;
    clock_gettime(CLOCK_MONOTONIC, &spec);
    time_ms = (spec.tv_sec*1000000UL) + (spec.tv_nsec / 0x1000UL);
    return time_ms;
}

static inline uint64_t systime_get_cycle(void) {
    unsigned long lo, hi;
    asm volatile ( "rdtsc" : "=a" (lo), "=d" (hi) );
    return (lo | (hi << 32));
}

static inline uint32_t systime_get_cycleh(void) {
    unsigned long lo, hi;
    asm volatile ( "rdtsc" : "=a" (lo), "=d" (hi) );
    return hi;
}

static inline uint32_t systime_get_cyclel(void) {
    unsigned long lo, hi;
    asm volatile ( "rdtsc" : "=a" (lo), "=d" (hi) );
    return lo;
}

#ifdef __cplusplus
}
#endif

#endif/*!__ASM_TICK_H*/
