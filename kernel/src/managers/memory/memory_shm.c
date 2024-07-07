#include <sentry/ktypes.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/managers/task.h>
#include <sentry/managers/memory.h>
#include <uapi/handle.h>

#include "memory_shm-dt.h"
#include "memory.h"

/**
 * shared memory configuration. This config is set by the owner.
 * at boot time, all fields are set to SECURE_FALSE
 */
typedef struct shm_config {
    secure_bool_t rw; /**< is SHM writable by the user ? */
    secure_bool_t transferable; /**< is SHM transferable by user to another ? */
} shm_config_t;

typedef struct shm_user_state {
    shm_config_t       config;
    secure_bool_t      is_mapped;
    taskh_t            task;
} shm_user_state_t;

typedef struct shm_info {
    shmh_t             handle;
    shm_meta_t  const *meta;
    secure_bool_t      is_mapped;
    secure_bool_t      is_shared;
    shm_user_state_t   owner;
    shm_user_state_t   user;
} shm_info_t;

static shm_info_t shm_table[SHM_LIST_SIZE];

/**
 * @fn initialize the SHM dynamic table
 *
 * This table is used for SHM dynamic actions such as mapping, unmapping,
 * credentials setting, sharing and so on.
 */
kstatus_t mgr_mm_shm_init(void)
{
    kstatus_t status = K_STATUS_OKAY;
    kshmh_t ksh;

    if (unlikely(mgr_mm_configured() == SECURE_TRUE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    for (size_t id = 0; id < SHM_LIST_SIZE; ++id) {
        uint32_t entropy;

        if (unlikely((status = mgr_security_entropy_generate(&entropy)) != K_STATUS_OKAY)) {
            goto end;
        }
        ksh.id = id;
        /* using 24 LSB bits for runtime randomness of shm handles */
        ksh.rng = (entropy & 0xffffff);
        shm_table[id].handle = *(kshmh_to_shmh(&ksh));
        shm_table[id].meta = memory_shm_get_meta(id);
        if (unlikely(shm_table[id].meta == NULL)) {
            /* this should never happen */
            panic(PANIC_CONFIGURATION_MISMATCH);
        }
        shm_table[id].is_shared = SECURE_FALSE;
        shm_table[id].owner.is_mapped = SECURE_FALSE;
        shm_table[id].owner.config.rw = SECURE_FALSE;
        shm_table[id].owner.config.transferable = SECURE_FALSE;
        status = mgr_task_get_handle(shm_table[id].meta->owner_label, &shm_table[id].owner.task);
        if (unlikely(status != K_STATUS_OKAY)) {
            goto end;
        }
        shm_table[id].user.is_mapped = SECURE_FALSE;
        shm_table[id].user.config.rw = SECURE_FALSE;
        shm_table[id].user.config.transferable = SECURE_FALSE;
        /* at init time, shm is not shared and user is owner */
        shm_table[id].user.task = shm_table[id].owner.task;
    }
end:
    return status;
}

/**
 * @brief specify if the given SHM can be mapped by owner or user
 *
 * the secure boolean information is set through result argument
 */
kstatus_t mgr_mm_shm_is_mappable(shmh_t handle, secure_bool_t *result)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&handle);
    /*@ assert \valid_read(kshm); */

    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (unlikely(result == NULL)) {
        goto end;
    }
    /*@ assert \valid(result); */
    /* check that id exsits */
    if (unlikely(kshm->id >= SHM_LIST_SIZE)) {
        goto end;
    }
    /* check that handle matches */
    if (unlikely(shm_table[kshm->id].handle != handle)) {
        goto end;
    }
    *result = shm_table[kshm->id].meta->is_mappable;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief specify if the given SHM is owned by the given task, using its handle
 *
 * the secure boolean information is set through result argument
 */
kstatus_t mgr_mm_shm_is_owned_by(shmh_t handle, taskh_t taskh, secure_bool_t*result)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&handle);
    /*@ assert \valid_read(kshm); */

    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (unlikely(result == NULL)) {
        goto end;
    }
    /*@ assert \valid(result); */
    /* check that id exsits */
    if (unlikely(kshm->id >= SHM_LIST_SIZE)) {
        goto end;
    }
    /* check that handle matches */
    if (unlikely(shm_table[kshm->id].handle != handle)) {
        goto end;
    }
    if (shm_table[kshm->id].owner.task == taskh) {
        *result = SECURE_TRUE;
    } else {
        *result = SECURE_FALSE;
    }
    status = K_STATUS_OKAY;
end:
    return status;
}

kstatus_t mgr_mm_shm_is_writeable_by(shmh_t handle, shm_user_t accessor, secure_bool_t*result)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&handle);
    /*@ assert \valid_read(kshm); */

    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (unlikely(result == NULL)) {
        goto end;
    }
    /*@ assert \valid(result); */
    /* check that id exsits */
    if (unlikely(kshm->id >= SHM_LIST_SIZE)) {
        goto end;
    }
    /* check that handle matches */
    if (unlikely(shm_table[kshm->id].handle != handle)) {
        goto end;
    }
    switch (accessor) {
        case SHM_TSK_OWNER:
            *result = shm_table[kshm->id].owner.config.rw;
            break;
        case SHM_TSK_USER:
            *result = shm_table[kshm->id].user.config.rw;
            break;
        default:
            goto end;
    }
    status = K_STATUS_OKAY;
end:
    return status;
}


/**
 * @brief specify if the given SHM is used by the given task, using its handle
 *
 * the secure boolean information is set through result argument
 */
kstatus_t mgr_mm_shm_is_used_by(shmh_t handle, taskh_t taskh, secure_bool_t *result)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&handle);
    /*@ assert \valid_read(kshm); */

    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (unlikely(result == NULL)) {
        goto end;
    }
    /*@ assert \valid(result); */
    /* check that id exsits */
    if (unlikely(kshm->id >= SHM_LIST_SIZE)) {
        goto end;
    }
    /* check that handle matches */
    if (unlikely(shm_table[kshm->id].handle != handle)) {
        goto end;
    }
    if (shm_table[kshm->id].user.task == taskh) {
        *result = SECURE_TRUE;
    } else {
        *result = SECURE_FALSE;
    }
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief specify if the given SHM is shared with another task
 *
 * the secure boolean information is set through result argument
 */
kstatus_t mgr_mm_shm_is_shared(shmh_t handle, secure_bool_t * result)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&handle);
    /*@ assert \valid_read(kshm); */

    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (unlikely(result == NULL)) {
        goto end;
    }
    /*@ assert \valid(result); */
    /* check that id exsits */
    if (unlikely(kshm->id >= SHM_LIST_SIZE)) {
        goto end;
    }
    /* check that handle matches */
    if (unlikely(shm_table[kshm->id].handle != handle)) {
        goto end;
    }
    *result = shm_table[kshm->id].is_shared;
    status = K_STATUS_OKAY;
end:
    return status;
}

kstatus_t mgr_mm_shm_is_mapped_by(shmh_t handle, shm_user_t accessor, secure_bool_t * result)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&handle);
    /*@ assert \valid_read(kshm); */

    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (unlikely(result == NULL)) {
        goto end;
    }
    /*@ assert \valid(result); */
    /* check that id exsits */
    if (unlikely(kshm->id >= SHM_LIST_SIZE)) {
        goto end;
    }
    /* check that handle matches */
    if (unlikely(shm_table[kshm->id].handle != handle)) {
        goto end;
    }
    switch (accessor) {
        case SHM_TSK_OWNER:
            *result = shm_table[kshm->id].owner.is_mapped;
            break;
        case SHM_TSK_USER:
            *result = shm_table[kshm->id].user.is_mapped;
            break;
        default:
            goto end;
    }
    status = K_STATUS_OKAY;
end:
    return status;
}

kstatus_t mgr_mm_shm_set_mapflag(shmh_t handle, shm_user_t accessor, secure_bool_t mapflag)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&handle);
    /*@ assert \valid_read(kshm); */

    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    /* check that id exsits */
    if (unlikely(kshm->id >= SHM_LIST_SIZE)) {
        goto end;
    }
    /* check that handle matches */
    if (unlikely(shm_table[kshm->id].handle != handle)) {
        goto end;
    }
    switch (accessor) {
        case SHM_TSK_OWNER:
            shm_table[kshm->id].owner.is_mapped = mapflag;
            break;
        case SHM_TSK_USER:
            shm_table[kshm->id].user.is_mapped = mapflag;
            break;
        default:
            goto end;
    }
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief given a shm id (as declared in DTS) returns the corresponding handle
 *
 * the secure boolean information is set through result argument
 */
kstatus_t mgr_mm_shm_get_handle(uint32_t shm_id, shmh_t *handle)
{
    kstatus_t status = K_ERROR_INVPARAM;

    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (unlikely(handle == NULL)) {
        goto end;
    }
    /*@ assert \valid(handle); */
    for (size_t index = 0; index < SHM_LIST_SIZE; ++index) {
        if (shm_table[index].meta->shm_label == shm_id) {
            *handle = shm_table[index].handle;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
end:
    return status;
}


kstatus_t mgr_mm_shm_get_meta(shmh_t handle, shm_meta_t const ** meta)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&handle);

    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (unlikely(meta == NULL)) {
        goto end;
    }
    /*@ assert \valid(meta); */
    if (unlikely(kshm->id >= SHM_LIST_SIZE)) {
        goto end;
    }
    /* check that handle matches */
    if (unlikely(shm_table[kshm->id].handle != handle)) {
        goto end;
    }
    *meta = shm_table[kshm->id].meta;
    status = K_STATUS_OKAY;
end:
    return status;
}
