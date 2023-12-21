// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ZLIB_MATH_H
#define ZLIB_MATH_H

#ifdef __cplusplus
extern "C" {
#endif

/* all calculation-related macros and primitives */

/**
 * @def padd the given value x to a value multiple of modulo, x included
 */
#define ROUND_UP_TO(x,modulo) ((x) + ((x)%(modulo)?(modulo)-((x)%(modulo)):0UL))


#ifdef __cplusplus
}
#endif

#endif/*!!ZLIB_MATH_H*/
