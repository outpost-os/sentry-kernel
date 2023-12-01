#include <inttypes.h>
#include <stdbool.h>

/* kernel includes */
#include <sentry/arch/asm-generic/platform.h>
#include <sentry/arch/asm-generic/membarriers.h>
#include <bsp/drivers/gpio/gpio.h>
#if CONFIG_ARCH_ARM_CORTEX_M
#include <sentry/arch/asm-cortex-m/systick.h>
#else
#error "unsupported platform"
#endif
#include <sentry/managers/io.h>
#include <sentry/managers/debug.h>
#include <sentry/managers/clock.h>
#include <sentry/managers/interrupt.h>
#include <sentry/managers/security.h>
#include <sentry/managers/task.h>
#include <sentry/managers/memory.h>
#include <sentry/sched.h>
#include <sentry/thread.h>

/* used for debug printing only */
extern uint32_t _bootupstack;

/*
 * address if the PSP idle stack, as defined in the layout (see m7fw.ld)
 */

#if __GNUC__
#if __clang__
# pragma clang optimize off
#else
__attribute__((optimize("-fno-stack-protector")))
#endif
#endif
__attribute__((noreturn)) void _entrypoint(void)
{
    /* early init phase */
    mgr_interrupt_early_init();

    /* init phase */
    mgr_mm_init();      /* memory protection active */
    mgr_clock_init();
    mgr_interrupt_init();
    mgr_io_init();
#ifdef CONFIG_BUILD_TARGET_DEBUG
    mgr_debug_init();
#endif
    pr_info("Starting Sentry kernel release %s", "v0.1");
    pr_info("kernel bootup stack at %p, current frame: %p", &_bootupstack, __platform_get_current_sp());
    pr_info("booting on SoC %s", CONFIG_ARCH_SOCNAME);
    pr_info("configured dts file: %s", CONFIG_DTS_FILE);
    /* end of basic platform initialization acknowledged */
    platform_init();
    pr_info("Platform initialization done, continuing with upper layers");
    mgr_security_init();

    sched_init();
    mgr_task_init();    /* list of tasks parsed (depend on sched_init) */
    mgr_device_init();  /* device list and task link forged (depend on task_init) */


    /* FIXME: to be added to a platform manager */
    //systick_init();
    /* memory protection active now. Any device access (including kernel ones)
       requires to voluntary map/unmap them */
    interrupt_enable();


#if 0
#if defined(CONFIG_USE_ICACHE) && (CONFIG_USE_ICACHE == 1)
    icache_enable();
#endif

#if defined(CONFIG_USE_DCACHE) && (CONFIG_USE_DCACHE == 1)
    dcache_enable();
#endif
    perfo_early_init();
    do {
        asm volatile("wfi");
    } while (1);
#endif
    pr_debug("starting userspace");
    mgr_task_start();
    __builtin_unreachable();
    /* This part of the function is never reached */
}
