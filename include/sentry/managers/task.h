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

typedef enum thread_state {
      THREAD_STATE_NOTSTARTED, /**< thread has not started yet. For not automatically started tasks */
      THREAD_STATE_READY,     /**< thread ready, wait for being scheduled */
      THREAD_STATE_SLEEPING, /**< sleeping, can be awoken by any ISR (wfi()-like) */
      THREAD_STATE_SLEEPING_DEEP, /**< deep sleep, IRQ deactivated for the given sleep time */
      THREAD_STATE_FAULT,     /**< userspace fault event, not schedulable */
      THREAD_STATE_SECURITY,  /**< security event risen, not schedulable */
      THREAD_STATE_ABORTING,  /**< on fault, handling abort-equivalent libc garbage collect. if the task
                                 implement a sigabrt() handler, the garbage collector execute the user-defined
                                 function before leaving */
      THREAD_STATE_FINISHED,  /**< thread terminated, returned from thread entrypoint */
      THREAD_STATE_IPC_SEND_BLOCKED, /**< emitted an IPC, wait for receiver to process */
      THREAD_STATE_IPC_SIG_RECV_BLOCKED, /**< listening on IPC&signals events but no event received by now */
} thread_state_t;

/**
 * TODO: to be moved to dedicated header
 * for a given task job, specify the spwaning mode
 */
typedef enum thread_flags {
    THREAD_FLAG_AUTOSTART     = 0x0001UL,
    THREAD_FLAG_RESTARTONEXIT = 0x0002UL,
    THREAD_FLAG_PANICONEXIT   = 0x0004UL,
} thread_flags_t;



/*@
  logic boolean thread_state_is_valid(uint32_t thread_state) =
    (
        thread_state == THREAD_STATE_NOTSTARTED ||
        thread_state == THREAD_STATE_READY ||
        thread_state == THREAD_STATE_SLEEPING ||
        thread_state == THREAD_STATE_SLEEPING_DEEP ||
        thread_state == THREAD_STATE_FAULT ||
        thread_state == THREAD_STATE_SECURITY ||
        thread_state == THREAD_STATE_ABORTING ||
        thread_state == THREAD_STATE_FINISHED ||
        thread_state == THREAD_STATE_IPC_SEND_BLOCKED ||
        thread_state == THREAD_STATE_IPC_SIG_RECV_BLOCKED
    );
*/

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
     * Task and struct identification part
     */
    uint64_t        magic;         /**< task structure magic number */
    uint32_t        version;       /**< structure version, may vary based on SDK version */
    taskh_t         handle;        /**< task identifier (see handle.h, starting with rerun=0) */
    uint8_t         priority;      /**< task priority */
    uint8_t         quantum;       /**< task configured quantum */
    uint16_t        capabilities;  /**< task capabilities mask */
    thread_flags_t  flags;         /**< general task flags (boot mode, etc.)*/

    /**
     * Memory mapping information, used for context switching and MPU configuration
     */
    size_t          s_text;           /**< start address of .text section */
    size_t          text_size;        /**< text section size */
    size_t          s_rodata;         /**< start address of .data section */
    size_t          rodata_size;      /**< text section size */
    size_t          si_data;           /**< start address of .data section */
    size_t          s_data;           /**< start address of .data section in SRAM */
    size_t          data_size;        /**< text section size */
    size_t          s_bss;            /**< start address of .bss is SRAM */
    size_t          bss_size;         /**< bss size in SRAM */
    uint16_t        main_offset;      /**< offset of main() in text section */
    size_t          stack_top;        /**< main thread stack top address */
    uint16_t        stack_size;       /**< main thtrad stack size */

    size_t          heap_base;        /**< process heap base. Always set */
    uint16_t        heap_size;        /**< process heap size. Can be 0 (no heap)*/

    /**
     * Task ressources, that may also requires memory mapping, and associated perms
     */
    uint8_t         num_shm;          /**< number of shared memories */
    uint8_t         shared_memory[CONFIG_MAX_SHM_PER_TASK];/**< SHM metadatas */ /* shm_t to define*/
    uint8_t         num_devs;         /**< number of devices */
    devh_t          devices[CONFIG_MAX_DEV_PER_TASK]; /**< devices metadata */
    uint8_t         num_dmas;         /**< number of DMA streams */
    uint8_t         dmas[CONFIG_MAX_DMA_STREAMS_PER_TASK]; /**< DMA streams metadata
                                        FIXME: define dma_t bitfield or struct */

    /**
     * domain management. Ignore if HAS_DOMAIN is not set
     */
    uint8_t         domain;           /**< domain identifier. Depending on the configured domain
                                            policy, process ability to communicate with others,
                                            process scheduling policy and process election
                                            pre- and post- phases may be affected.
                                             */


    /*
     * Security part: the structure itself and the associated task memory
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

kstatus_t mgr_task_watchdog(void);

/*
 * About module specific API
 */

stack_frame_t *mgr_task_initialize_sp(size_t sp, size_t pc);

uint32_t mgr_task_get_num(void);

kstatus_t mgr_task_get_sp(taskh_t t, stack_frame_t **sp);

kstatus_t mgr_task_get_state(taskh_t t, thread_state_t *state);

kstatus_t mgr_task_get_metadata(taskh_t t, const task_meta_t **tsk_meta);

kstatus_t mgr_task_set_sp(taskh_t t, stack_frame_t *newsp);

kstatus_t mgr_task_set_state(taskh_t t, thread_state_t state);

secure_bool_t mgr_task_is_idletask(taskh_t t);

secure_bool_t mgr_task_handle_exists(taskh_t t);

kstatus_t mgr_task_get_device_owner(devh_t d, taskh_t *t);

#ifdef __cplusplus
}
#endif

#endif/*!SECURITY_MANAGER_H*/
