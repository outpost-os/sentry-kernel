#ifndef TASK_MANAGER_H
#define TASK_MANAGER_H

#ifdef __cplusplus
extern "C" {
#endif


#include <assert.h>
#include <inttypes.h>
#include <stddef.h>

#include <uapi/handle.h>
#include <uapi/capability.h>
#include <sentry/managers/device.h>
#include <sentry/dma.h>
#include <sentry/ipc.h>
#include <sentry/signal.h>
#include <sentry/ktypes.h>
#include <sentry/job.h>

/**
 * \file sentry kernel generic types
 */

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/thread.h>
#elif defined(__x86_64__)
#include <sentry/arch/asm-x86_64/thread.h>
#elif defined(__i386__)
#include <sentry/arch/asm-i386/thread.h>
#else
#error "unsupported architecture!"
#endif

/**
 * @def no task label definition
 *
 * At early bootup, before any task is started (even idle), the scheduler returns
 * a specially forged task label denoted 'babe'. This label is forbidden to user
 * tasks and used to detect 'no task exists at all, still in MSP bootup'
 */
#define SCHED_NO_TASK_LABEL   0xbabeUL

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
    taskh_t         handle;        /**< task identifier (see handle.h, starting with rerun=0) */
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

stack_frame_t *mgr_task_initialize_sp(size_t sp, size_t pc);

uint32_t mgr_task_get_num(void);

kstatus_t mgr_task_get_sp(taskh_t t, stack_frame_t **sp);

kstatus_t mgr_task_get_state(taskh_t t, job_state_t *state);

kstatus_t mgr_task_get_metadata(taskh_t t, const task_meta_t **tsk_meta);

kstatus_t mgr_task_set_sp(taskh_t t, stack_frame_t *newsp);

kstatus_t mgr_task_set_state(taskh_t t, job_state_t state);

secure_bool_t mgr_task_is_idletask(taskh_t t);

secure_bool_t mgr_task_handle_exists(taskh_t t);

kstatus_t mgr_task_get_device_owner(devh_t d, taskh_t *t);

size_t mgr_task_get_data_region_size(const task_meta_t *meta);

size_t mgr_task_get_text_region_size(const task_meta_t *meta);

/* specialized event pushing API, do not use directly but instead Generic below */
kstatus_t mgr_task_push_inth_event(irqh_t ev, taskh_t t);
kstatus_t mgr_task_push_ipch_event(ipch_t ev, taskh_t t);
kstatus_t mgr_task_push_sigh_event(sigh_t ev, taskh_t t);

/**
 * @def generic task manager event pushing API
 *
 * pushing interrupts (inth_t), IPC (ipch_t) or signals (sigh_t) to a job through
 * its taskh_t identifier.
 * If the target task is waiting for an event, the task is set ready again and
 * readded to the scheduler.
 */
#define mgr_task_push_event(T, t) _Generic((T),  \
              irqh_t:  mgr_task_push_inth_event, \
              ipch_t:  mgr_task_push_ipch_event, \
              sigh_t:  mgr_task_push_sigh_event  \
        ) (T, t)

#ifdef __cplusplus
}
#endif

#endif/*!SECURITY_MANAGER_H*/
