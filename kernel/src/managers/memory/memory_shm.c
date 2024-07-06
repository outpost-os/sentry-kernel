#include <sentry/ktypes.h>
#include <uapi/handle.h>
#include "memory_shm-dt.h"

/**
 * shared memory configuration. This config is set by the owner.
 * at boot time, all fields are set to SECURE_FALSE
 */
typedef struct shm_config {
    secure_bool_t rw; /**< is SHM writable by the user ? */
    secure_bool_t transferable; /**< is SHM transferable by user to another ? */
} shm_config_t;

typedef struct shm_info {
    shm_meta_t  const *meta;
    secure_bool_t      is_mapped;
    secure_bool_t      is_shared;
    shm_config_t       config;
    taskh_t            owner;
    taskh_t            user;
} shm_info_t;

static shm_info_t shm_table[SHM_LIST_SIZE];

kstatus_t mgr_mm_shm_init(void)
{
    kstatus_t status = K_STATUS_OKAY;

    return status;
}

kstatus_t mgr_mm_shm_is_mappable(shmh_t handle, secure_bool_t *result)
{
    return K_ERROR_INVPARAM;
}

kstatus_t memory_shm_is_owned_by(shmh_t shm, taskh_t taskh, secure_bool_t*result)
{
    return K_ERROR_INVPARAM;
}

kstatus_t mgr_mm_shm_is_used_by(shmh_t shm, taskh_t taskh, secure_bool_t *result)
{
    return K_ERROR_INVPARAM;
}

kstatus_t mgr_mm_shm_is_shared(shmh_t shm, secure_bool_t * result)
{
    return K_ERROR_INVPARAM;
}

kstatus_t mgr_mm_shm_get_handle(uint32_t shm_id, shmh_t *handle)
{
    return K_ERROR_INVPARAM;
}
