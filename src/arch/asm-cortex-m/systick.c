// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <inttypes.h>
#include <assert.h>


#include <sentry/arch/asm-generic/interrupt.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/arch/asm-cortex-m/systick.h>
#include <bsp/drivers/clk/rcc.h>
#include <sentry/io.h>


// FIXME: systick registers defs is in cmsis (core.h)
#define SCB_SYSTICK_CSR    (SysTick_BASE + 0x0u)

#define SCB_SYSTICK_CSR_ENA_Pos (0u)
#define SCB_SYSTICK_CSR_ENA_Msk (0x1u)

typedef enum scb_systick_enable {
    SCB_SYSTICK_TIMER_DISABLE = 0,
    SCB_SYSTICK_TIMER_ENABLE = 1,
} scb_systick_enable_t;


#define SCB_SYSTICK_CSR_TICKINT_Pos (1u)
#define SCB_SYSTICK_CSR_TICKINT_Msk (0x1u)

typedef enum scb_systick_tickint {
    SCB_SYSTICK_TICKINT_DISABLE = 0,
    SCB_SYSTICK_TICKINT_ENABLE = 1,
} scb_systick_tickint_t;

#define SCB_SYSTICK_CSR_CLKSRC_Pos (2u)
#define SCB_SYSTICK_CSR_CLKSRC_Msk (0x1u)

typedef enum scb_systick_clksource {
    SCB_SYSTICK_CLKSRC_EXT = 0,
    SCB_SYSTICK_CLKSRC_CPU = 1,
} scb_systick_clksource_t;

#define SCB_SYSTICK_CSR_CNTFLAG_Pos (16u)
#define SCB_SYSTICK_CSR_CNTFLAG_Msk (0x1u)

#define SCB_SYSTICK_RVR    (SysTick_BASE + 0x4u)

#define SCB_SYSTICK_RVR_RELOAD_Pos (0u)
#define SCB_SYSTICK_RVR_RELOAD_Msk (0x00ffffffu)

#define SCB_SYSTICK_CVR    (SysTick_BASE + 0x8u)

#define SCB_SYSTICK_CVR_CURRENT_Pos (0u)
#define SCB_SYSTICK_CVR_CURRENT_Msk (0x00ffffffu)

#define SCB_SYSTICK_CALIB  (SysTick_BASE + 0xCu)

#define SCB_SYSTICK_CALIB_TENMS_Pos (0u)
#define SCB_SYSTICK_CALIB_TENMS_Msk (0x00ffffffu)

#define SCB_SYSTICK_CALIB_SKEW_Pos (30u)
#define SCB_SYSTICK_CALIB_SKEW_Msk (0x1u)

typedef enum scb_systick_clkskew {
    SCB_SYSTICK_CLKSKEW_CALIB_VALID = 0,
    SCB_SYSTICK_CLKSKEW_CALIB_INVALID = 1,
} scb_systick_clkskew_t;

#define SCB_SYSTICK_CALIB_NOREF_Pos (31u)
#define SCB_SYSTICK_CALIB_NOREF_Msk (0x1u)

typedef enum scb_systick_clkref {
    SCB_SYSTICK_CLKREF_AVAILABLE = 0,
    SCB_SYSTICK_CLKREF_UNAVAILABLE = 1,
} scb_systick_clkref_t;

static uint64_t jiffies;
static uint64_t wait_jiffies;

static inline void store_wait_jiffies(uint64_t jiffies_to_wait)
{
    /*
     * There is no way to load/store atomically double word on cortex M architecture
     * so, the only available method is with irq dis/en, a.k.a. critical section or spinlock in the
     * very case of single core processor.
     * XXX: add a proper handling to this, i.e. with the following use case:
     *  - critical section enter while irq are disabled (do not enable interrupt unintendedly)
     *  - nested critical section (? do we need this ? do we need).
     * TODO: the easy way to do this is a spinlock_lock_irqsave/spinlock_unlock_irqrestore function
     * and with BASEPri CortexM register.
     */
    interrupt_disable();
    wait_jiffies = jiffies_to_wait;
    interrupt_enable();
}

static inline uint64_t load_wait_jiffies(void)
{
    uint64_t wait;

    interrupt_disable();
    wait = wait_jiffies;
    interrupt_enable();

    return wait;
}

/*
 * By now, while we do not use timer or external based wait mechanism,
 * the following implementation is used for waiting:
 * the wait(ms) function set a counter with ms+1,
 * and arm the pendsv handler. Each time the systick is being executed, if there
 * is a waiter, (ms+1 value is bigger than 0), the value is decremented.
 * If the value is 0, the systick stops decrement, the wait() stops waiting.
 *
 * **DO NOT CALL** from interrupt
 */
void wait(unsigned long long ms)
{
    jiffies_t wait = MSEC_TO_JIFFIES(ms + 1);

    store_wait_jiffies(wait);
    request_data_membarrier();

    do {
        /* XXX: do we spin or wait here */
        asm volatile ("nop");
    } while (load_wait_jiffies() > 0);
}

static void systick_calibrate(void)
{
    uint64_t freq = rcc_get_core_frequency();
    uint64_t reload =  freq / CONFIG_SYSTICK_HZ;

    iowrite32(SCB_SYSTICK_CSR, 0);
    iowrite32(SCB_SYSTICK_CVR, 0);
    iowrite32(SCB_SYSTICK_RVR, (uint32_t)reload - 1);
}

uint64_t systime_get_jiffies(void)
{
    return jiffies;
}

void systick_init(void)
{
    uint32_t reg;

    static_assert(CONFIG_SYSTICK_HZ > 0, "system tick frequency MUST NOT be null");

    jiffies = 0ULL;
    wait_jiffies = 0ULL;

    systick_calibrate();
    /* enable interrupt, set clksource as CPU clock */
    reg  = ((SCB_SYSTICK_CLKSRC_CPU & SCB_SYSTICK_CSR_CLKSRC_Msk) << SCB_SYSTICK_CSR_CLKSRC_Pos) |
           ((SCB_SYSTICK_TIMER_ENABLE & SCB_SYSTICK_CSR_ENA_Msk) << SCB_SYSTICK_CSR_ENA_Pos) |
           ((SCB_SYSTICK_TICKINT_ENABLE & SCB_SYSTICK_CSR_TICKINT_Msk) << SCB_SYSTICK_CSR_TICKINT_Pos);
    iowrite32(SCB_SYSTICK_CSR, reg);
#if defined(CONFIG_WITH_LIBTIMER) && CONFIG_WITH_LIBTIMER == 1
    static_assert(CONFIG_SYSTICK_HZ >= 1000, "system tick frequency MUST NOT be bigger than 1KHz");
    static_assert((CONFIG_SYSTICK_HZ % 1000) == 0, "system tick must be 1ms multiple");
    timer_set_period(CONFIG_SYSTICK_HZ / 1000);
#endif
}

void systick_stop_and_clear(void)
{
    iowrite32(SCB_SYSTICK_CSR, 0UL);
    iowrite32(SCB_SYSTICK_RVR, 0UL);
    iowrite32(SCB_SYSTICK_CVR, 0UL);
    SCB->ICSR |= SCB_ICSR_PENDSTCLR_Msk;
}

stack_frame_t *systick_handler(stack_frame_t * stack_frame)
{
    jiffies++;

    if (wait_jiffies > 0) {
        wait_jiffies--;
    }
    return stack_frame;
}
