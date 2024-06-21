// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ZLIB_GCC_H
#define ZLIB_GCC_H

#ifndef ZLIB_COMPILER_H
#error "error: do not include this file directly!"
#endif

#if __STDC_VERSION__ == 201112L

#define __MAYBE_UNUSED __attribute__((unused))
#define __UNUSED __attribute__((unused))

#endif/*! std C11 */


/* C23 compilation use case */
#if __STDC_VERSION__ == 202311L

#define __MAYBE_UNUSED __attribute__((maybe_unused))
#define __UNUSED __attribute__((unused))

#endif/*! std C23 */

#endif/*!ZLIB_GCC_H */
