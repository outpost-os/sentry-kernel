// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ARCH_LAYOUT_GENERIC_H
#define ARCH_LAYOUT_GENERIC_H

/**
 * \file local SoC layout entrypoint
 */

#if defined(__arm__) || defined(__FRAMAC__)
#include <sentry/arch/asm-cortex-m/layout.h>
#endif

#endif/*ARCH_LAYOUT_GENERIC_H*/
