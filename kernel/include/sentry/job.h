// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef JOB_H
#define JOB_H

/**
 * \file job types and generic definitions
 */

/**
 * These are job start mode possible values (bitfield)
 */
#define JOB_FLAG_NOSTART     0
#define JOB_FLAG_AUTOSTART   1

/**
 * These are job exit mode possible values (bitfield)
 */
#define JOB_FLAG_NORESTARTONEXIT 0
#define JOB_FLAG_RESTARTONEXIT   1
#define JOB_FLAG_PANICONEXIT     2
#define JOB_FLAG_PERIODICRESTART 3

/*
 * this header is used for Sentry JSON schema generation. To avoid C content
 * inclusion in Json, only macro content is kept
 */
#ifndef SCHEMA_GENERATION
typedef enum job_state {
      JOB_STATE_NOTSTARTED = 0,       /**< thread has not started yet. For not automatically started tasks */
      JOB_STATE_READY,                /**< thread ready, wait for being scheduled */
      JOB_STATE_SLEEPING,             /**< sleeping, can be awoken by any ISR (wfi()-like) */
      JOB_STATE_SLEEPING_DEEP,        /**< deep sleep, IRQ deactivated for the given sleep time */
      JOB_STATE_FAULT,                /**< userspace fault event, not schedulable */
      JOB_STATE_SECURITY,             /**< security event risen, not schedulable */
      /**< on fault, handling abort-equivalent libc garbage collect. if the task
        implement a sigabrt() handler, the garbage collector execute the user-defined
        function before leaving */
      JOB_STATE_ABORTING,
      JOB_STATE_FINISHED,             /**< thread terminated, returned from thread entrypoint */
      JOB_STATE_IPC_SEND_BLOCKED,     /**< emitted an IPC, wait for receiver to process */
      JOB_STATE_IPC_SIG_RECV_BLOCKED, /**< listening on IPC&signals events but no event received by now */
} job_state_t;

/**
 * @struct job flags register
 * define the way a job is started and exited, based on bitfields
 */
typedef struct __attribute__((packed)) job_flags {
    unsigned int start_mode: 1;
    unsigned int exit_mode:  2;
    unsigned int reserved:   5;
} job_flags_t;
static_assert((sizeof(job_flags_t) == sizeof(uint8_t)), "job_flags_t as invalid size!");
/*@
  logic boolean job_state_is_valid(uint32_t job_state) =
    (
        job_state == JOB_STATE_NOTSTARTED ||
        job_state == JOB_STATE_READY ||
        job_state == JOB_STATE_SLEEPING ||
        job_state == JOB_STATE_SLEEPING_DEEP ||
        job_state == JOB_STATE_FAULT ||
        job_state == JOB_STATE_SECURITY ||
        job_state == JOB_STATE_ABORTING ||
        job_state == JOB_STATE_FINISHED ||
        job_state == JOB_STATE_IPC_SEND_BLOCKED ||
        job_state == JOB_STATE_IPC_SIG_RECV_BLOCKED
    );
*/
#endif

#endif/*!JOB_H*/
