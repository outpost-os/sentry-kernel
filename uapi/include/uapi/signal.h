// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef UAPI_SIGNAL_H
#define UAPI_SIGNAL_H

#include <stdint.h>

typedef enum signal {
    SIGNAL_ABORT = 1,   /**< Abort signal */
    SIGNAL_ALARM,       /**< timer (from alarm) */
    SIGNAL_BUS,         /**< bus error (bad memory access, memory required)*/
    SIGNAL_CONT,        /**< continue if previously stopped */
    SIGNAL_ILL,         /**< illegal instruction. Can be also used for upper protocols */
    SIGNAL_IO,          /**< I/O now ready */
    SIGNAL_PIPE,        /**< broken pipe */
    SIGNAL_POLL,        /**< event pollable */
    SIGNAL_TERM,        /**< termination signal. Can be used to stop an IPC stream for e.g. (remote process termination is not possible) */
    SIGNAL_TRAP,        /**< trace/bp signal (debug usage )*/
    SIGNAL_USR1,        /**< 1st user-defined signal */
    SIGNAL_USR2,        /**< 2nd user-defined signal */
} signal_t;

#endif/*!UAPI_SIGNAL_H*/
