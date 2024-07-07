#ifndef MEMORY_PRIVATE_H
#define MEMORY_PRIVATE_H

#include <sentry/ktypes.h>
#include <uapi/handle.h>
#include <sentry/managers/memory.h>
#include "memory_shm-dt.h"

/**
 * @brief kernel-level shmh encoding
 *
 * Only memory manager knows it, opaque for others
 * NOTE: this requires security manager to be started before memory manager
 */
typedef struct kshmh {
    uint32_t id : 8;       /**< SHM local table index */
    uint32_t rng : 24;     /**< handle randomness, boot time */
} kshmh_t;

static_assert(sizeof(kshmh_t) == sizeof(uint32_t), "SHM opaque sizing failed!");

union ush {
    const shmh_t *sh;
    const kshmh_t *ksh;
};

 /**
  * @fn shmh_to_kshmh convert an opaque shm handler to a structured handler
  *
  * @param sh input shm handler
  *
  * @return converted handler to structured value
  */
static inline const kshmh_t *shmh_to_kshmh(const shmh_t * const sh) {
    /*@ assert \valid(sh); */
    union ush converter = {
        .sh = sh
    };
    return converter.ksh;
}

 /**
  * @fn kshmh_to_shmh convert a structured shm handler to an opaque handler
  *
  * @param ksh input structured shm handler
  *
  * @return converted handler to opaque value
  */
static inline const shmh_t *kshmh_to_shmh(const kshmh_t * const ksh) {
    /*@ assert \valid(kdh); */
    union ush converter = {
        .ksh = ksh
    };
    return converter.sh;
}

kstatus_t mgr_mm_shm_init(void);

kstatus_t mgr_mm_shm_get_meta(shmh_t handle, shm_meta_t const ** meta);

kstatus_t mgr_mm_shm_set_mapflag(shmh_t handle, shm_user_t accessor, secure_bool_t mapflag);

kstatus_t mgr_mm_map_kernel_txt(void);

kstatus_t mgr_mm_map_kernel_data(void);

secure_bool_t mgr_mm_configured(void);

#endif/*!MEMORY_PRIVATE_H*/
