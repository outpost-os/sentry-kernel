#ifndef TASK_MANAGER_H
#define TASK_MANAGER_H

#ifdef __cplusplus
extern "C" {
#endif


#include <assert.h>
#include <inttypes.h>
#include <stddef.h>

#include <uapi/uapi.h>
#include <uapi/handle.h>
#include <uapi/capability.h>
#include <sentry/managers/device.h>
#include <sentry/dma.h>
#include <sentry/ipc.h>
#include <sentry/ktypes.h>
#include <sentry/job.h>

/**
 * \file sentry kernel generic types
 */
#include <sentry/arch/asm-generic/thread.h>
#include <sentry/arch/asm-generic/memory.h>
/**
 * @def idle task label definition
 *
 * When no task of the user task set is schedulable, the idle task is the lonely
 * task eligible. This special task is a dedicated thread that wfi() and yield()
 * so that the core can enter SLEEP mode while no interrupt rise and all tasks
 * are blocked (external event wait, sleep, etc.).
 * The idle task has a dedicated label denoted 'cafe'. This label is forbidden
 * to user tasks.
 */
#define SCHED_IDLE_TASK_LABEL 0xcafeUL

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
/**
 * @def no task label for autotest
 *
 * Autotest exists only in autotest mode, when no other task but autotest and idle
 * exist. It is used for automatic kernel testing/fuzzing, with remote control if needed
 * so that the Sentry kernel features can be properly verified.
 * See the autotest application for more information.
 */
#define SCHED_AUTOTEST_TASK_LABEL 0xbabeUL
#endif

/**
 * This is the main task structure manipulated by the kernel. Each task build (ELF generation)
 * produce a blob that contain such binary format.
 * The structure is generated using as input:
 * - the ELF metadatas
 * - the task informations (permissions, configuration, dts information, etc.)
 * - the task label (16 bits unique identifier, like, for e.g. 0xbabe or 0x1051)
 *
 * when generated, the task structure is stored as a standalone file in the build system
 * so that it can be easily dumped by python tooling, and also pushed into the kernel image
 * in a dedicated task list section where all tasks info are stored.
 */
typedef struct task_meta {
    /**
     * Task metadata identification part
     */
    uint64_t        magic;         /**< task structure magic number */
    uint32_t        version;       /**< structure version, may vary based on SDK version */

    /**
     * Task identification and generic configuration part
     */
    uint32_t        label;         /**< task unique identifier (32 bits label) */
    uint8_t         priority;      /**< task priority */
    uint8_t         quantum;       /**< task configured quantum */
    uint32_t        capabilities;  /**< task capabilities mask */
    job_flags_t     flags;         /**< general task flags (boot mode, etc.)*/

    /**
     * domain management. Ignore if HAS_DOMAIN is not set
     */

    /**< domain identifier. Depending on the configured domain
        policy, process ability to communicate with others,
        process scheduling policy and process election
        pre- and post- phases may be affected.
    */
    uint8_t         domain;

    /**
     * Task memory mapping information, used for context switching and MPU configuration
     * Using all of these, the task manager can fully forge the task RAM mapping, using
     * the following layout:
     *  RAM (RW-)      FLASH (R-X)
     * [ stack ]      [ rodata ]
     * [ heap  ]      [ text   ]
     * [ bss   ]
     * [ data  ]
     * [ svc-e ]
     *
     * As a consequence, only svc-e and text base address is required. Overall region
     * size is a basic addition of each section size, starting from the corresponding
     * base address
     */
    size_t          s_text;           /**< start address of .text section */
    size_t          text_size;        /**< text section size */
    size_t          s_got;            /**< start address of .got section */
    size_t          got_size;         /**< got section size */
    size_t          rodata_size;      /**< text section size */
    size_t          data_size;        /**< .data section size */
    size_t          bss_size;         /**< bss size in SRAM */
    size_t          heap_size;        /**< process heap size. Can be 0 (no heap)*/
    size_t          s_svcexchange;    /**< SVC exchange area start in RAM. address is project-wide defined */
    uint16_t        stack_size;       /**< main thtrad stack size */
    uint16_t        entrypoint_offset; /**< offset of _start in text section */
    uint16_t        finalize_offset;   /**< offset of the _finalize in text section */

    /**
     * Task ressources, that may also requires memory mapping, and associated perms
     */
    uint8_t         num_shm;          /**< number of shared memories */
    shmh_t          shms[CONFIG_MAX_SHM_PER_TASK];/**< SHM metadatas */ /* shm_t to define*/
    uint8_t         num_devs;         /**< number of devices */
    devh_t          devs[CONFIG_MAX_DEV_PER_TASK]; /**< devices metadata */
    uint8_t         num_dmas;         /**< number of DMA streams */
    dmah_t          dmas[CONFIG_MAX_DMA_STREAMS_PER_TASK]; /**< DMA streams metadata
                                        FIXME: define dma_t bitfield or struct */

    /*
     * Task integrity part: the structure itself and the associated task memory
     * is checked using HMAC, based on a private key used at production time and
     * verified by the kernel at startup time
     */
    uint8_t         task_hmac[32]; /**< task .text+.rodata+.data build time hmac calculation (TBD)*/
    uint8_t         metadata_hmac[32]; /**< current struct build time hmac calculation */
} task_meta_t;

/*
 * About main module standardly defined functions (init, watchdog....)
 */

kstatus_t mgr_task_init(void);

void __attribute__((noreturn)) mgr_task_start(void);

kstatus_t mgr_task_watchdog(void);

/*
 * About module specific API
 */

stack_frame_t *mgr_task_initialize_sp(uint32_t rerun, size_t sp, size_t pc, size_t got);

uint32_t mgr_task_get_num(void);

kstatus_t mgr_task_get_sp(taskh_t t, stack_frame_t **sp);

kstatus_t mgr_task_get_state(taskh_t t, job_state_t *state);

kstatus_t mgr_task_get_metadata(taskh_t t, const task_meta_t **tsk_meta);

kstatus_t mgr_task_get_handle(uint32_t label, taskh_t *handle);

kstatus_t mgr_task_set_sp(taskh_t t, stack_frame_t *newsp);

kstatus_t mgr_task_set_state(taskh_t t, job_state_t state);

secure_bool_t mgr_task_is_idletask(taskh_t t);

secure_bool_t mgr_task_handle_exists(taskh_t t);

kstatus_t mgr_task_get_device_owner(devh_t d, taskh_t *t);

size_t mgr_task_get_data_region_size(const task_meta_t *meta);

size_t mgr_task_get_text_region_size(const task_meta_t *meta);

secure_bool_t mgr_task_is_userspace_spawned(void);

taskh_t mgr_task_get_idle(void);

/**
 * @brief Add (map) a mappable resource to the task current layout
 *
 * @param t task handle
 * @param resource_id resource layout index in task layout table
 * @param resource resource to add
 */
kstatus_t mgr_task_add_resource(taskh_t t, uint8_t resource_id, layout_resource_t resource);

/**
 * @brief Remove the resource identified by its id from the task current layout
 *
 * @param t task handle
 * @param resource_id resource layout index in task layout table
 */
kstatus_t mgr_task_remove_resource(taskh_t t, uint8_t resource_id);


kstatus_t mgr_task_get_layout_from_handle(taskh_t t, const layout_resource_t **layout);

/**
 * @brief get back current sysreturn value of a job
 *
 * Fails if the syscall return field is set as cleared
 */
kstatus_t mgr_task_get_sysreturn(taskh_t t, Status *sysret);

/**
 * @brief Set the currently called syscall return value of job identified by t
 *
 * Can be set synchronously by its own syscall or by another job's syscall
 */
kstatus_t mgr_task_set_sysreturn(taskh_t t, Status sysret);

/**
 * @brief clear curently set syscall return
 *
 * this will make all consecutive call to task_get_sysreturn failing
 */
kstatus_t mgr_task_clear_sysreturn(taskh_t t);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
taskh_t mgr_task_get_autotest(void);

kstatus_t mgr_task_autotest(void);
#endif

/* specialized event pushing API, do not use directly but instead Generic below */
kstatus_t mgr_task_push_int_event(uint32_t IRQn, taskh_t dest);
kstatus_t mgr_task_push_ipc_event(uint32_t len, taskh_t source, taskh_t dest);
kstatus_t mgr_task_push_sig_event(uint32_t sig, taskh_t source, taskh_t dest);


typedef struct exchange_event {
    uint8_t type;   /*< event type, as defined in uapi/types.h */
    uint8_t length; /*< event data length, depending on event */
    uint16_t magic; /*< event TLV magic, specific to input event reception */
    uint8_t data[]; /*< event data, varies depending on length field */
} exchange_event_t;

kstatus_t mgr_task_load_ipc_event(taskh_t context);
kstatus_t mgr_task_load_sig_event(taskh_t context);
kstatus_t mgr_task_load_int_event(taskh_t context);

#ifdef __cplusplus
}
#endif

#endif/*!SECURITY_MANAGER_H*/
