// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file STM32F3xx and F4xx PLL & clock driver (see ST RM0090 datasheet)
 */
#include <assert.h>
#include <stdbool.h>

#include <sentry/arch/asm-cortex-m/soc.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/io.h>
#include <sentry/bits.h>
#include <sentry/ktypes.h>
#include <sentry/zlib/crypto.h>
#include <sentry/managers/memory.h>
#include <bsp/drivers/clk/rcc.h>
#include "rng_defs.h"
#include "stm32-rng-dt.h"


#define MAX_RNG_TRIES   16U
#define RNG_RDY_TIMEOUT 0x5000

static bool rng_enabled;
static bool not_first_rng;
static uint32_t last_rng_crc;

static inline kstatus_t rng_map(void)
{
    stm32_rng_desc_t const * desc = stm32_rng_get_desc();
    return mgr_mm_map_kdev(desc->base_addr, desc->size);
}
/* for simplicity sake, but unmaping a kernel device is generic */
static inline kstatus_t rng_unmap(void) {
    return mgr_mm_unmap_kdev();
}

/**
 * @brief Initialize RNG
 *
 * @param nothing
 * @return nothing
 */
/*@
  @ assigns *(uint32_t*)(RNG_BASE_ADDR .. RNG_BASE_ADDR + RNG_DR_REG);
  @ ensures rng_enabled == \true <==> \result == K_STATUS_OKAY;
  @ ensures \result == K_STATUS_OKAY ||
            \result == K_ERROR_BADCLK ||
            \result == K_ERROR_NOTREADY ||
            \result == K_ERROR_BADENTROPY;
  @*/
kstatus_t rng_probe(void)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t reg = 0;
    int ready_timeout = 0;
    stm32_rng_desc_t const * rng_desc = stm32_rng_get_desc();
    /* BSS is zeroified at boot, should be false at startup */
    if (unlikely(rng_enabled)) {
        status = K_ERROR_BADSTATE;
        goto err;
    }
    rng_enabled = false;
    if (unlikely((status = rcc_enable(rng_desc->bus_id, rng_desc->clk_msk, RCC_NOFLAG)) != K_STATUS_OKAY)) {
        goto err;
    }
    if (unlikely((status = rng_map()) != K_STATUS_OKAY)) {
        goto err;
    }
    /* Enable random number generation */
    reg |= RNG_CR_RNGEN;
    iowrite(RNG_BASE_ADDR + RNG_CR_REG, reg);
    /* Wait for the RNG to be ready */
    while (!(ioread32(RNG_BASE_ADDR + RNG_SR_REG) & RNG_SR_DRDY)) {
        ready_timeout++;
        if (ready_timeout == RNG_RDY_TIMEOUT) {
            status = K_ERROR_NOTREADY;
            goto err;
        }
    };
    /* Check for error */
    reg = ioread32(RNG_BASE_ADDR + RNG_SR_REG);
    if (unlikely(reg & RNG_SR_CEIS)) {
        /* Clear error */
        reg ^= RNG_SR_CEIS;
        iowrite(RNG_BASE_ADDR + RNG_SR_REG, reg);
        status = K_ERROR_BADCLK;
        goto err;
    }
    if (unlikely(reg & RNG_SR_SEIS)) {
        reg ^= RNG_SR_SEIS;
        iowrite(RNG_BASE_ADDR + RNG_SR_REG, reg);
        /* reset RNG enable bit */
        iowrite(RNG_BASE_ADDR + RNG_SR_REG, reg & (~RNG_CR_RNGEN));
        iowrite(RNG_BASE_ADDR + RNG_SR_REG, reg);
        status = K_ERROR_BADENTROPY;
        goto err;
    }
    last_rng_crc = 0;
    not_first_rng = 0;
    rng_enabled = true;
    rng_unmap();
err:
    return status;
}

/*@
  @ requires \valid(random);
  @ assigns *random;
  @ ensures rng_enabled == \false <==> \result == K_ERROR_BADSTATE;
  @ ensures \result == K_STATUS_OKAY ||
            \result == K_ERROR_NOTREADY ||
            \result ==  K_SECURITY_FIPSCOMPLIANCE;
  @*/
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
    if (unlikely(not_first_rng == false)) {
        not_first_rng =true;
        /* instead of keeping the random value itself for FIPS compliance,
         * we use its CRC32 calculation. Enough to detect collision, avoid
         * clear text random storage in memory
         */
        last_rng_crc = crc;
        status = K_SECURITY_FIPSCOMPLIANCE;
        goto err;
    }
    if (last_rng_crc == crc) {
        /* FIPS PUB test of current with previous random (here CRC comparison)
         * if CRC are equal, dismiss current random value
         */
        last_rng_crc = crc;
        status = K_SECURITY_FIPSCOMPLIANCE;
        goto err;
    }
    last_rng_crc = crc;
    status = K_STATUS_OKAY;
err:
    return status;
}


/*@
  @ assigns *random;
  @ ensures random == NULL <==> \result == K_ERROR_INVPARAM;
  @ ensures (rng_enabled == \false) <==> \result == K_ERROR_BADSTATE;
  @ ensures !(random == NULL && rng_enabled == \false) <==>
  @    \result == K_STATUS_OKAY ||
  @    \result == K_ERROR_NOTREADY ||
  @    \result == K_SECURITY_FIPSCOMPLIANCE;
  @*/
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

    if (unlikely(rng_enabled) == 0) {
        status = K_ERROR_BADSTATE;
        goto err;
    }
    if (random == NULL) {
        status = K_ERROR_INVPARAM;
        goto err;
    }
    if (unlikely((status = rng_map()) != K_STATUS_OKAY)) {
        goto err;
    }
    /*@ assert \valid(random); */
    /*@
      @ loop assigns status, max_rng_count;
      @ loop variant MAX_RNG_TRIES - max_rng_count ;
    */
    do {
        status = rng_load(random);
        max_rng_count++;
        if (max_rng_count > MAX_RNG_TRIES) {
            goto err;
        }
    } while (status != K_STATUS_OKAY);
    rng_unmap();
err:
    return status;
}
