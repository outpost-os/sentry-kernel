#ifndef __ASM_TICK_H
#define __ASM_TICK_H

#include <stddef.h>
#include <inttypes.h>
#include <sentry/arch/asm-cortex-m/systick.h>

void systime_init(void);

uint64_t systime_get_cycle(void);

/**
 * return the high word of the cycle counter
 */
static inline  uint32_t systime_get_cycleh(void)
{
    uint64_t cycles = systime_get_cycle();
    return (uint32_t)((cycles >> 32) & 0xffffffffUL);
}

/**
 * return the low word of the cycle counter
 */
static inline uint32_t systime_get_cyclel(void)
{
    uint64_t cycles = systime_get_cycle();
    return (uint32_t)(cycles & 0xffffffffUL);
}

__attribute__((always_inline))
static inline uint64_t systime_get_seconds(void)
{
    return JIFFIES_TO_SEC(systime_get_jiffies());
}

__attribute__((always_inline))
static inline uint64_t systime_get_milliseconds(void)
{
    return JIFFIES_TO_MSEC(systime_get_jiffies());
}

__attribute__((always_inline))
static inline uint64_t systime_get_microseconds(void) {
    uint64_t ts = systime_get_cycleh();
    uint32_t freq = rcc_get_core_frequency();
    /* divide freq by number of micros in 1 sec */
    freq /= 1000000UL;
    ts <<= 32;
    ts |= systime_get_cyclel();
    ts /= freq;
    return ts;
}



#endif/*!__ASM_TICK_H*/
