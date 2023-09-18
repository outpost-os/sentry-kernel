// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file I/O manipulation primitive
 */

#ifndef BITS_H
#define BITS_H

#include <inttypes.h>
#include <assert.h>

/**
 * @brief Helper to forge a bit field for one bit
 * @param n bit number
 *
 * Here, it is safe to use unsigned long which is the same size as machine word
 * (except for exotic hardware or OSes such as Windows...)
 */
#define BIT(n) (1UL << (n))

/**
 * @brief Assert if BITFIELD is ill-formed
 */
#define __BITFIELD_SANITY_CHECK(e,s) static_assert((e) >= (s), "bitfield end bit must be greater or equal than start bit")

/**
 * @brief Generate a shifted bit mask for a register field.
 *
 * @param e ending bit number of the field
 * @param s starting bit number of the field
 *
 * @todo: add build time check on register width (some IP has 8bits register bank)
 */
/*#define BITFIELD_MASK(e, s) (uint32_t)(((1ULL << ((e) - (s) + 1)) - 1) << (s))*/
#define BITFIELD_MASK(e, s) \
({ \
    __BITFIELD_SANITY_CHECK(e,s); \
    (uint32_t)(((1ULL << ((e) - (s) + 1)) - 1) << (s)); \
})

/**
 * @brief Gives the bit number (starting from 0) of the first bit set in mask
 *
 * It is assumed that the mask is a valid bitfield mask (i.e. forged with BITFIELD_MASK(e, s))
 * This macro use `ffs` (find first set) intrinsic which returns the first bit set position,
 * starting from 1.
 *
 * Here, we do not use `ctz` (count trailing zero) which may gave a direct bit shift w/o
 * subtraction except in case of zeroed mask. ctz(O) == word bit size which leads
 * to a valid shift despite the obvious error in this case.
 * ffs(0) == 0, w/ subtraction, it produces `shift-count-overflow` warning.
 *
 * @note private (this header) usage only
 */
#define __BITSHIFT_FROM_MASK(x) (__builtin_ffsl((long)(x)) - 1)

/**
 * @brief Shifted and masked a value to be written in a bitfield (e.g. a register)
 * such value may be combined w/ other field using `|` (i.e. OR) operator.
 *
 * @param x bitfield value to put in
 * @param m bitfield mask
 */
#define BITFIELD_PUT(x, m) (((x) << __BITSHIFT_FROM_MASK((m))) & (uint32_t)(m))

/**
 * @brief extract a field value from register
 * returned value is masked and unsifted.
 *
 * @param x register value
 * @param m register field mask
 */
#define BITFIELD_GET(x, m) (((x) & (uint32_t)(m)) >> __BITSHIFT_FROM_MASK(m))

#endif/*BITS_H*/
