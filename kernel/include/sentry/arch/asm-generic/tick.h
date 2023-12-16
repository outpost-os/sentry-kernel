// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef TICK_H
#define TICK_H

#ifdef __cplusplus
extern "C" {
#endif

#if defined(__arm__)
#include <sentry/arch/asm-cortex-m/systick.h>
#include <sentry/arch/asm-cortex-m/tick.h>
#elif defined(__x86_64__)
#include <sentry/arch/asm-x86_64/tick.h>
#endif

#ifdef __cplusplus
}
#endif

#endif/*TICK_H*/
