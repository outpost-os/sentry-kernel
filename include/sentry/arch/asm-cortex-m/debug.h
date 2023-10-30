// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef __DEBUG_H
#define __DEBUG_H

#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/ktypes.h>

/**
  @brief detect if a debugger is connected to the board

  using the standard ARM debug register, check if the core freeze flag is
  enabled, meaning that a JTAG probe is connected to the board.

  @return SECURE_TRUE if the probe is detected using this method, or SECURE_FALSE
  */
static inline secure_bool_t __dbg_debugger_is_connected(void) {
    secure_bool_t   res = SECURE_FALSE;
    CoreDebug_Type* debug = CoreDebug;

    if ((debug->DHCSR & CoreDebug_DHCSR_C_DEBUGEN_Msk) != 0) {
        res = SECURE_TRUE;
    }
    return res;
}

#endif/*__DEBUG_H*/
