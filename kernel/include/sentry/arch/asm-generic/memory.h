// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ARCH_GEN_MEMORY_H
#define ARCH_GEN_MEMORY_H

/**
 * \file memory protection entrypoint
 */

#ifdef __cplusplus
extern "C" {
#endif

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/mpu.h>
#endif

#ifdef __cplusplus
}
#endif

#endif/*!#ifndef ARCH_GEN_MEMORY_H*/
