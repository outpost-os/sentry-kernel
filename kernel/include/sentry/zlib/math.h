// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef ZLIB_MATH_H
#define ZLIB_MATH_H

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief basic generic min scalar comparison macro
 * returned value is one of (the smaller between) a or b
 *
 * @param a scalar value (any numeric value)
 * @param b scalar value (any numeric value)
 */
#define MIN(a,b) ((a) > (b) ? (b) : (a))

/**
 * @brief basic generic max scalar comparison macro
 * returned value is one of (the bigger between) a or b
 *
 * @param a scalar value (any numeric value)
 * @param b scalar value (any numeric value)
 */
#define MAX(a,b) (((a) > (b)) ? (a) : (b))

/**
 * @def DIV_ROUND_UP(n, d)
 * @brief integer division rounded to the upper integer
 * @param n numerator (a.k.a. dividend)
 * @param d denominator (a.k.a. divisor)
 * @note This is Euclidean division quotient, `+1` if remainder is not null
 */
#define DIV_ROUND_UP(n, d) (((n) + (d) - 1) / (d))

/**
 * @brief Round up `n` to the next `m` multiple
 *
 * `ROUND_UP(n, m) % m == 0`
 *
 * @param n number to round up
 * @param m number to align to
 *
 * @note if `m` is a power of two, use ROUND_UP_POW2 instead
 */
#define ROUND_UP(n, m) (DIV_ROUND_UP(n,m) * (m))

/**
 * @brief True if `s` is a power of 2
 */
#define IS_POW2(s) ((s != 0) && ((s & (s - 1)) == 0))

/**
 * @brief Round up 'n' to the next 'm' multiple, 'm' must be a power of two
 */
#define ROUND_UP_POW2(n, p) ( \
{ \
  static_assert(IS_POW2(p), "ROUND_UP_POW2 must be used w/ power of 2"); \
  ((((n) - 1) | ((p) - 1)) + 1); \
} \
)

/**
 * @brief Align `s` to the next power of two
 */
#define ALIGN_TO_POW2(s) (1 << (32 - __builtin_clz (s - 1)))


#ifdef __cplusplus
}
#endif

#endif/*!!ZLIB_MATH_H*/
