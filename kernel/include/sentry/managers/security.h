#ifndef SECURITY_MANAGER_H
#define SECURITY_MANAGER_H

#ifdef __cplusplus
extern "C" {
#endif

#include <uapi/uapi.h>

/**
 * @file Sentry I/O manager API
 */

typedef enum capability {
    CAP_DEV_BUSES        = (0x1UL  << 0),
    CAP_DEV_IO           = (0x1UL  << 1),
    CAP_DEV_DMA          = (0x1UL  << 2),
    CAP_DEV_ANALOG       = (0x1UL  << 3),
    CAP_DEV_TIMER        = (0x1UL  << 4),
    CAP_DEV_STORAGE      = (0x1UL  << 5),
    CAP_DEV_CRYPTO       = (0x1UL  << 6),
    CAP_DEV_CLOCK        = (0x1UL  << 7),
    CAP_DEV_POWER        = (0x1UL  << 8),
    CAP_DEV_NEURAL       = (0x1UL  << 9),
    CAP_SYS_UPGRADE      = (0x1UL  << 12),
    CAP_SYS_POWER        = (0x1UL  << 13),
    CAP_SYS_PROCSTART    = (0x1UL  << 14),
    CAP_MEM_SHM_OWN      = (0x1UL  << 16),
    CAP_MEM_SHM_USE      = (0x1UL  << 17),
    CAP_MEM_SHM_TRAHSFER = (0x1UL  << 18),
    CAP_TIM_HP_CHRONO    = (0x1UL  << 20),
    CAP_CRY_KRNG         = (0x1UL  << 21),
} capability_t;

/** @def mask for dev capability. dev capa hold 11 first bytes of register */
#define CAP_DEV_MASK ((0x1UL  << 12) - 1)
/** @def mask for sys capability, hold bits 12-15 */
#define CAP_SYS_MASK (((0x1UL  << 16) - 1) & ~CAP_DEV_MASK)
/*@ def mask for mem capability */
#define CAP_MEM_MASK (((0x1UL << 20) - 1) & ~(CAP_DEV_MASK | CAP_SYS_MASK))


#include <sentry/ktypes.h>

kstatus_t mgr_security_init(void);

kstatus_t mgr_security_entropy_generate(uint32_t *seed);

kstatus_t mgr_security_get_capa(taskh_t tsk, uint32_t *capas);

secure_bool_t mgr_security_has_dev_capa(taskh_t tsk);

secure_bool_t mgr_security_has_sys_capa(taskh_t tsk);

secure_bool_t mgr_security_has_capa(taskh_t tsk, capability_t  capa);

secure_bool_t mgr_security_has_oneof_capas(taskh_t tsk, uint32_t capas);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_security_autotest(void);
#endif

#ifdef __cplusplus
}
#endif

#endif/*!SECURITY_MANAGER_H*/
