// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ZLIB_COMPILER_H
#define ZLIB_COMPILER_H

#ifdef __cplusplus
extern "C" {
#endif

#if defined(__FRAMAC__)
#include <sentry/zlib/backends/framac.h>
#elif defined(__GNUC__)
#include <sentry/zlib/backends/gcc.h>
#elif defined(__clang__)
#include <sentry/zlib/backends/clang.h>
#endif

#ifdef __cplusplus
}
#endif

#endif/*!ZLIB_COMPILER_H*/
