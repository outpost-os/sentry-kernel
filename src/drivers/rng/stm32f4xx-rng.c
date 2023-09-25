// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file STM32F3xx and F4xx PLL & clock driver (see ST RM0090 datasheet)
 */
#include <assert.h>
#include <stdbool.h>
#include <stdatomic.h>

#include <sentry/arch/asm-cortex-m/soc.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/io.h>
#include <sentry/bits.h>
#include <sentry/ktypes.h>
#include <sentry/crypto/crc32.h>
#include "../clk/rcc_defs.h"
#include "rng_defs.h"


#define MAX_RNG_TRIES   16U

static atomic_bool rng_enabled;
static atomic_bool not_first_rng;
static atomic_uint last_rng_crc;

/**
 * @brief Initialize RNG (mainly initialize it clock).
 *
 * @param nothing
 * @return nothing
 */
kstatus_t rng_probe(void)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t reg = 0;
    /* BSS is zeroified at boot, should be false at startup */
    if (unlikely(atomic_load(&rng_enabled))) {
        status = K_ERROR_BADSTATE;
        goto err;
    }
    rng_enabled = ATOMIC_VAR_INIT(false);
    /* FIXME: enable clock through clk API */
    iowrite32(RCC_AHB2ENR_REG, RCC_AHB2ENR_RNGEN);

    /* Enable random number generation */
    reg |= RNG_CR_RNGEN;
    iowrite32(RNG_BASE_ADDR + RNG_CR_REG, reg);
    /* Wait for the RNG to be ready */
    while (!(ioread32(RNG_BASE_ADDR + RNG_SR_REG) & RNG_SR_DRDY)) {
        /** FIXME: timeout to add here */
    };
    /* Check for error */
    reg = ioread32(RNG_BASE_ADDR + RNG_SR_REG);
    if (unlikely(reg & RNG_SR_CEIS)) {
        /* Clear error */
        reg ^= RNG_SR_CEIS;
        iowrite32(RNG_BASE_ADDR + RNG_SR_REG, reg);
        status = K_ERROR_BADCLK;
        goto err;
    }
    if (unlikely(reg & RNG_SR_SEIS)) {
        reg ^= RNG_SR_SEIS;
        iowrite32(RNG_BASE_ADDR + RNG_SR_REG, reg);
        /* reset RNG enable bit */
        iowrite32(RNG_BASE_ADDR + RNG_SR_REG, reg & (~RNG_CR_RNGEN));
        iowrite32(RNG_BASE_ADDR + RNG_SR_REG, reg);
        status = K_ERROR_BADENTROPY;
        goto err;
    }
    atomic_store(&last_rng_crc, 0);
    atomic_store(&not_first_rng, 0);
    atomic_store(&rng_enabled, true);
err:
    return status;
}

/**
 * @brief Run the random number genrator.
 *
 * Run the RNG to get a random number. return 0 if
 * generation is completed, or an error code if not.
 *
 * As explained in FIPS PUB, we discard the first
 * random number generated and compare each generation
 * to the next one. Each number has to be compared to
 * previous one and generation fails if they're equal.
 *
 * @param  random Random number buffer.
 * @return 0 if success, error code is failure.
 */
static inline kstatus_t rng_load(uint32_t * random)
{
    kstatus_t status = K_STATUS_OKAY;
    uint32_t crc;

    /* Check RNG readyness first */
    if (unlikely((ioread32(RNG_BASE_ADDR + RNG_SR_REG) & RNG_SR_DRDY) == 0)) {
        status = K_ERROR_NOTREADY;
        goto err;
    }
    /* read RNG number from RNG */
    *random = ioread32(RNG_BASE_ADDR + RNG_DR_REG);

    /* FIPS check: if first RNG or previous & current RNG identical,
     * FIPS error
     */
    crc = crc32((uint8_t*)random, sizeof(uint32_t), 0xffffffffu);
    if (unlikely(atomic_load(&not_first_rng) == false)) {
        atomic_store(&not_first_rng, true);
        /* instead of keeping the random value itself for FIPS compliance,
         * we use its CRC32 calculation. Enough to detect collision, avoid
         * clear text random storage in memory
         */
        atomic_store(&last_rng_crc, crc);
        status = K_SECURITY_FIPSCOMPLIANCE;
        goto err;
    }
    if (last_rng_crc == crc) {
        /* FIPS PUB test of current with previous random (here CRC comparison)
         * if CRC are equal, dismiss current random value
         */
        atomic_store(&last_rng_crc, crc);
        status = K_SECURITY_FIPSCOMPLIANCE;
        goto err;
    }
    atomic_store(&last_rng_crc, crc);
    status = K_STATUS_OKAY;
err:
    return status;
}

/**
 * @brief Launch a random number generation and handles errors.
 *
 * @param random Random number buffer
 */
kstatus_t rng_get(uint32_t * random)
{
    kstatus_t status = K_STATUS_OKAY;
    uint8_t ret;
    bool seed_ok = false;
    uint8_t max_rng_count = 0;

    if (unlikely(atomic_load(&rng_enabled))) {
        status = K_ERROR_BADSTATE;
        goto err;
    }
    if (random == NULL) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    do {
        status = rng_load(random);
        max_rng_count++;
        if (max_rng_count > MAX_RNG_TRIES) {
            goto err;
        }
    } while (status != K_STATUS_OKAY);
err:
    return status;
}
