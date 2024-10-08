// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <stdarg.h>
#include <string.h>
#include <inttypes.h>
#include <stdbool.h>
#include <sentry/ktypes.h>
#include <sentry/managers/debug.h>
#include "log_lexer.h"

/***********************************************
 * local utility functions
 **********************************************/

/*
 * Stdio functions (*printf) use a local ring buffer
 * to hold formated content before sending it to the
 * kernel via the kernel log API (typically sys_log()
 * for EwoK).
 * This ring buffer is holded in the libstd as a global
 * variable, local to this very file.
 * The ring buffer is initialized by the libstd at
 * application boot time, as the libstd is managing the
 * application starting point, including the ring buffer
 * and stack canaries initialization in the do_starttask()
 * function.
 *
 * All the ring-buffer associated function, used only by
 * the stdio functions, are implemented here.
 */

/*
 * Print the ring buffer content (if there is some), and reset its
 * state to empty state.
 * The ring buffer is also memset'ed to 0.
 *
 * The buffer content is sent to the kernel log API.
 */
kstatus_t dbgbuffer_display(void)
{
    return debug_rawlog((uint8_t*)log_get_dbgbuf(), log_get_dbgbuf_offset());
}


/*************************************************************
 * libstream exported API implementation: POSIX compilant API
 ************************************************************/

/*
 * Linux-like printk() API (no kernel tagging by now)
 */
__attribute__ ((format (printf, 1, 2))) kstatus_t printk(const char *fmt, ...)
{
    kstatus_t status = K_ERROR_INVPARAM;
    va_list args;
    size_t  len;


    if (unlikely(fmt == NULL)) {
        goto err;
    }
    /*
     * if there is some asyncrhonous printf to pass to the kernel, do it
     * before execute the current printf command
     */
    va_start(args, fmt);
    if (likely(print_with_len(fmt, &args, &len) == 0)) {
        status = K_STATUS_OKAY;
    }
    va_end(args);
    if (unlikely(status != K_STATUS_OKAY)) {
        dbgbuffer_flush();
        goto err;
    }
    /* display to debug output */
    dbgbuffer_display();

err:
    dbgbuffer_flush();
    return status;
}
