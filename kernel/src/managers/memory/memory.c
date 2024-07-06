#include <inttypes.h>
#include <sentry/arch/asm-generic/panic.h>
#include "memory.h"

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/mpu.h>
#elif defined(__x86_64__)
// TODO add core,mmu and handler headers (or minimum to compile)
#elif defined(__i386__)
// TODO add core,mmu and handler headers (or minimum to compile)
#else
#error "unsupported architecture!"
#endif


static secure_bool_t mm_configured;

secure_bool_t mgr_mm_configured(void)
{
    if (mm_configured == SECURE_TRUE) {
        return mm_configured;
    }
    return SECURE_FALSE;
}

/*
 * @brief initialize MPU and configure kernel layout
 *
 * layout is the following:
 *
 * In kernel mode (syscalls):
 *                                                     S     U
 * [MPU REG 0] [ kernel TXT section                ] [R-X] [---]
 * [MPU REG 1] [ kernel DATA section               ] [RW-] [---]
 * [MPU REG 2] [ kernel current device, if needed  ] |RW-] [---] SO
 * [MPU REG 3] [ task Data SVC-exchange region     ] [RW-] [RW-]
 * [MPU REG 4] [                                   ] [---] [---]
 * [MPU REG 5] [                                   ] [---] [---]
 * [MPU REG 6] [                                   ] [---] [---]
 * [MPU REG 7] [                                   ] [---] [---]
 *
 * In User mode:
 *
 * [MPU REG 0] [ kernel TXT section                ] [R-X] [---] // syscall gate
 * [MPU REG 1] [ kernel DATA section               ] [RW-] [---] // syscall gate
 * [MPU REG 2] [ task TXT section                  ] [R-X] [R-X]
 * [MPU REG 3] [ task Data section                 ] [RW-] [RW-]
 * [MPU REG 4] [ task ressources bank 1, if needed ] [---] [---]
 * [MPU REG 5] [ task ressources bank 1, if needed ] [---] [---]
 * [MPU REG 6] [ task ressources bank 1, if needed ] [---] [---]
 * [MPU REG 7] [ task ressources bank 1, if needed ] [---] [---]
 *
 */
kstatus_t mgr_mm_init(void)
{
    kstatus_t status = K_STATUS_OKAY;
    mm_configured = SECURE_FALSE;

    if (unlikely((status = mgr_mm_shm_init()) != K_STATUS_OKAY)) {
        goto err;
    }
#ifdef CONFIG_HAS_MPU
    mpu_disable();
    status = mgr_mm_map_kernel_txt();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    status = mgr_mm_map_kernel_data();
    if (unlikely(status != K_STATUS_OKAY)) {
        goto err;
    }
    mpu_enable();
    mm_configured = SECURE_TRUE;
#endif
err:
    return status;
}
