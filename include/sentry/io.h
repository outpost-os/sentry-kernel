// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file I/O manipulation primitive
 */

#ifndef IO_H
#define IO_H

#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <assert.h>
#include <stdbool.h>

/* dispatcher for I/O file based on compiler host value */
#ifdef CONFIG_ARCH_ARM_CORTEX_M
#include <sentry/arch/asm-cortex-m/io.h>
#else
#error "unsupported architecture"
#endif

/** @brief Generic iowrite interface that implicitely handle multiple sizes */
#define iowrite(reg, T) _Generic((T),   \
              size_t:   iowrite32,      \
              uint32_t: iowrite32,      \
              uint16_t: iowrite16,      \
              uint8_t:  iowrite8        \
        ) (reg, T)

/**
 * @brief  Writes one byte at given address
 *
 * @param addr destination address
 * @param val byte to write
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline void iowrite8(size_t addr, uint8_t val)
{
    __iowrite8(addr, val);
}

/**
 * @brief  Writes an half-word at given address
 *
 * @param addr destination address
 * @param val half-word to write
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline void iowrite16(size_t addr, uint16_t val)
{
    __iowrite16(addr, val);
}

/**
 * @brief  Writes a word at given address
 *
 * @param addr destination address
 * @param val word to write
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline void iowrite32(size_t addr, uint32_t val)
{
    __iowrite32(addr, val);
}

/**
 * @brief  Reads one byte from given address
 *
 * @param addr source address
 * @return readden byte
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline uint8_t ioread8(size_t addr)
{
    return __ioread8(addr);
}

/**
 * @brief  Reads an half-word from given address
 *
 * @param addr source address
 * @return readden half-word
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline uint16_t ioread16(size_t addr)
{
    return __ioread16(addr);
}

/**
 * @brief  Reads a word from given address
 *
 * @param addr source address
 * @return readden word
 *
 * @note this function is always inline
 */
__attribute__((always_inline))
static inline uint32_t ioread32(size_t addr)
{
    return __ioread32(addr);
}

#endif /* IO_H */
