// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ARM_SYSTEM_H
#define ARM_SYSTEM_H

/**
 * \file ARM system layout definition (ARM standard)
 */
#include "soc.h"


/* NVIC related content */
#if defined(CONFIG_HAS_NVIC) && (CONFIG_HAS_NVIC == 1)
#include <sentry/arch/asm-generic/interrupt.h>
/* including CMSIS headers*/
#endif


#endif/*!ARM_SYSTEM_H*/
