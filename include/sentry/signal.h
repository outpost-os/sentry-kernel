// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef SIGNAL_H
#define SIGNAL_H

#include <stdint.h>

/** Basic signals that are handled at UAPI level. If more
  complex signal handling is required, IPC with upper layer protocol
  is needed.
  These signal can be used in order to avoid any memory copy, only scheduling
  the peer. The kernel guarantee that the signal is transmitted to the peer, but
  not that the peer do check for it (it is under the peer implementation responsability
  to handle a single blocking point with an input event blocking method that wait for,
  at least, signals).
  In IoT condition, these signals can be used for multiple usage while they keep the
  initial POSIX scementic.
  The standard POSIX USR1 and 2 signals are also defined to allow tasks to communicate
  through these two signals for custom events
  The userspace POSIX implementation of signals can be based on the sentry signal support,
  to avoid IPC-based data transmission for most signal events. INFO: by now, no spawned sighandler
  is supported, instead, a wait_for_event() call can be made in the main thread. Spawning
  threads is complex and do consume a lot of memory.
*/
typedef enum signal {
    SIGNAL_ABORT,   /**< Abort signal */
    SIGNAL_ALARM,   /**< timer (from alarm) */
    SIGNAL_BUS,     /**< bus error (bad memory access, memory required)*/
    SIGNAL_CONT,    /**< continue if previously stopped */
    SIGNAL_ILL,     /**< illegal instruction. Can be also used for upper protocols */
    SIGNAL_IO,      /**< I/O now ready */
    SIGNAL_PIPE,    /**< broken pipe */
    SIGNAL_POLL,    /**< event pollable */
    SIGNAL_TERM,    /**< termination signal. Can be used to stop an IPC stream for e.g. (remote process termination is not possible) */
    SIGNAL_TRAP,    /**< trace/bp signal (debug usage )*/
    SIGNAL_USR1,    /**< 1st user-defined signal */
    SIGNAL_USR2,    /**< 2nd user-defined signal */
} signal_t;

typedef struct signal_context {
    uint32_t tbd;
} signal_context_t;

#endif/*SIGNAL_H*/
