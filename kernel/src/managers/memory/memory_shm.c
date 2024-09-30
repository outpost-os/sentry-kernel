// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <sentry/ktypes.h>
#include <sentry/arch/asm-generic/panic.h>
#include <sentry/managers/task.h>
#include <sentry/managers/memory.h>
#include <uapi/handle.h>

#include "memory_shm-dt.h"
#include "memory.h"



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

#if SHM_LIST_SIZE > 0
    /* useless, size-limit warn, if shm list is empty */
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
        /*@ assert \valid_read(shm_table[id].meta); */
        shm_table[id].is_shared = SECURE_FALSE;
        shm_table[id].owner.is_mapped = SECURE_FALSE;
        shm_table[id].owner.config.rw = SECURE_FALSE;
        shm_table[id].owner.config.transferable = SECURE_FALSE;
        shm_table[id].owner.config.mappable = SECURE_FALSE;
        if (unlikely(mgr_task_get_handle( shm_table[id].meta->owner_label, &shm_table[id].owner.task) != K_STATUS_OKAY)) {
            /* this should never happen: dts task label invalid! */
            panic(PANIC_CONFIGURATION_MISMATCH);
        }
        shm_table[id].user.is_mapped = SECURE_FALSE;
        shm_table[id].user.config.rw = SECURE_FALSE;
        shm_table[id].user.config.transferable = SECURE_FALSE;
        shm_table[id].user.config.mappable = SECURE_FALSE;
        /* at init time, shm is not shared and user is owner */
        shm_table[id].user.task = shm_table[id].owner.task;
    }
end:
#endif
    return status;
}

kstatus_t mgr_mm_shm_get_task_type(shmh_t shm, taskh_t task, shm_user_t *accessor)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);
    /*@ assert \valid_read(kshm); */

    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (unlikely(accessor == NULL)) {
        goto end;
    }
    /*@ assert \valid(accessor); */
    /* check that id exsits */
    if (unlikely(kshm->id >= SHM_LIST_SIZE)) {
        goto end;
    }
    /* check that handle matches */
    if (unlikely(shm_table[kshm->id].handle != shm)) {
        goto end;
    }
    /* at boot time, task handle is not link as not yet forged. At first call, this
     * function cache it in local table to avoid task requests from label
     */
    if (shm_table[kshm->id].owner.task == task) {
        *accessor = SHM_TSK_OWNER;
    } else if (shm_table[kshm->id].user.task == task) {
        *accessor = SHM_TSK_USER;
    } else {
        *accessor = SHM_TSK_NONE;
    }
    status = K_STATUS_OKAY;
end:
    return status;
}

kstatus_t mgr_mm_shm_declare_user(shmh_t shm, taskh_t task)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);
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
    if (unlikely(shm_table[kshm->id].handle != shm)) {
        goto end;
    }
    shm_table[kshm->id].user.task = task;
    if (task != shm_table[kshm->id].owner.task) {
        shm_table[kshm->id].is_shared = SECURE_TRUE;
    } else {
        /* unsharing */
        shm_table[kshm->id].is_shared = SECURE_FALSE;
    }
end:
    return status;
}

/**
 * @fn get base address of the given SHM
 *
 * @param[in] shm: Shared memory handle that identify the SHM
 * @param[out] base: base address of the SHM returned when found
 */
kstatus_t mgr_mm_shm_get_baseaddr(shmh_t shm, size_t *base)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);

    /*@ assert \valid_read(kshm); */

    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (unlikely(base == NULL)) {
        goto end;
    }
    /*@ assert \valid(base); */
    /* check that id exsits */
    if (unlikely(kshm->id >= SHM_LIST_SIZE)) {
        goto end;
    }
    /* check that handle matches */
    if (unlikely(shm_table[kshm->id].handle != shm)) {
        goto end;
    }
    *base = shm_table[kshm->id].meta->baseaddr;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @fn get size in bytes of the given SHM
 *
 * @param[in] shm: Shared memory handle that identify the SHM
 * @param[out] size:  length in bytes of the SHM returned when found
 */
kstatus_t mgr_mm_shm_get_size(shmh_t shm, size_t *size)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);

    /*@ assert \valid_read(kshm); */

    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (unlikely(size == NULL)) {
        goto end;
    }
    /*@ assert \valid(size); */
    /* check that id exsits */
    if (unlikely(kshm->id >= SHM_LIST_SIZE)) {
        goto end;
    }
    /* check that handle matches */
    if (unlikely(shm_table[kshm->id].handle != shm)) {
        goto end;
    }
    *size = shm_table[kshm->id].meta->size;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @fn get label defined in DTS for the given SHM
 *
 * @param[in] shm: Shared memory handle that identify the SHM
 * @param[out] label: identifier of the SHM as declared in the DTS, returned when found
 */
kstatus_t mgr_mm_shm_get_label(shmh_t shm, uint32_t *label)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);

    /*@ assert \valid_read(kshm); */

    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    if (unlikely(label == NULL)) {
        goto end;
    }
    /*@ assert \valid(label); */
    /* check that id exsits */
    if (unlikely(kshm->id >= SHM_LIST_SIZE)) {
        goto end;
    }
    /* check that handle matches */
    if (unlikely(shm_table[kshm->id].handle != shm)) {
        goto end;
    }
    *label = shm_table[kshm->id].meta->shm_label;
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief specify if the given SHM can be mapped by owner or user
 *
 * the secure boolean information is set through result argument
 */
kstatus_t mgr_mm_shm_is_mappable_by(shmh_t shm, shm_user_t tsk, secure_bool_t *result)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);
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
    if (unlikely(shm_table[kshm->id].handle != shm)) {
        goto end;
    }
    /* whatever the local map flag is, when not mappable, just not mappable */
    if (shm_table[kshm->id].meta->is_mappable == SECURE_FALSE) {
        *result = SECURE_FALSE;
        status = K_STATUS_OKAY;
        goto end;
    }
    /* otherwise, check for requester */
    if (tsk == SHM_TSK_OWNER) {
        *result = shm_table[kshm->id].owner.config.mappable;
    } else {
        *result = shm_table[kshm->id].user.config.mappable;
    }
    status = K_STATUS_OKAY;
end:
    return status;
}

/**
 * @brief specify if the given SHM is owned by the given task, using its handle
 *
 * the secure boolean information is set through result argument
 */
kstatus_t mgr_mm_shm_is_owned_by(shmh_t shm, taskh_t taskh, secure_bool_t*result)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);
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
    if (unlikely(shm_table[kshm->id].handle != shm)) {
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

kstatus_t mgr_mm_shm_is_writeable_by(shmh_t shm, shm_user_t accessor, secure_bool_t*result)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);
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
    if (unlikely(shm_table[kshm->id].handle != shm)) {
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
kstatus_t mgr_mm_shm_is_used_by(shmh_t shm, taskh_t taskh, secure_bool_t *result)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);
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
    if (unlikely(shm_table[kshm->id].handle != shm)) {
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
kstatus_t mgr_mm_shm_is_shared(shmh_t shm, secure_bool_t * result)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);
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
    if (unlikely(shm_table[kshm->id].handle != shm)) {
        goto end;
    }
    *result = shm_table[kshm->id].is_shared;
    status = K_STATUS_OKAY;
end:
    return status;
}

kstatus_t mgr_mm_shm_is_mapped_by(shmh_t shm, shm_user_t accessor, secure_bool_t * result)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);
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
    if (unlikely(shm_table[kshm->id].handle != shm)) {
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

kstatus_t mgr_mm_shm_set_mapflag(shmh_t shm, shm_user_t accessor, secure_bool_t mapflag)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);
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
    if (unlikely(shm_table[kshm->id].handle != shm)) {
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
#if SHM_LIST_SIZE > 0
    /* useless, size-limit warn, if shm list is empty */
    for (size_t index = 0; index < SHM_LIST_SIZE; ++index) {
        if (shm_table[index].meta->shm_label == shm_id) {
            *handle = shm_table[index].handle;
            status = K_STATUS_OKAY;
            goto end;
        }
    }
#endif
end:
    return status;
}


kstatus_t mgr_mm_shm_get_meta(shmh_t shm, shm_meta_t const ** meta)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);

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
    if (unlikely(shm_table[kshm->id].handle != shm)) {
        goto end;
    }
    *meta = shm_table[kshm->id].meta;
    status = K_STATUS_OKAY;
end:
    return status;
}

kstatus_t mgr_mm_shm_configure(shmh_t shm, shm_user_t target, shm_config_t const *config)
{
    kstatus_t status = K_ERROR_INVPARAM;
    kshmh_t const *kshm = shmh_to_kshmh(&shm);

    /*@ assert \valid_read(kshm); */
    if (unlikely(mgr_mm_configured() == SECURE_FALSE)) {
        status = K_ERROR_BADSTATE;
        goto end;
    }
    /* check that id exsits */
    if (unlikely(kshm->id >= SHM_LIST_SIZE)) {
        goto end;
    }
    /* is this a real handle ? */
    if (unlikely(shm != shm_table[kshm->id].handle)) {
        goto end;
    }
    if (unlikely(config == NULL)) {
        goto end;
    }
    switch (target) {
        case SHM_TSK_OWNER:
            shm_table[kshm->id].owner.config.rw = config->rw;
            shm_table[kshm->id].owner.config.transferable = config->transferable;
            shm_table[kshm->id].owner.config.mappable = config->mappable;
            break;
        case SHM_TSK_USER:
            shm_table[kshm->id].user.config.rw = config->rw;
            shm_table[kshm->id].user.config.transferable = config->transferable;
            shm_table[kshm->id].user.config.mappable = config->mappable;
            break;
        default:
            goto end;
    }
    status = K_STATUS_OKAY;
end:
    return status;
}
