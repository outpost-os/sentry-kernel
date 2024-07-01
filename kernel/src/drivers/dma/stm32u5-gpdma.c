// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <sentry/ktypes.h>
#include "stm32-gpdma-dt.h"
#include "gpdma_defs.h"

/**
 * NOTE: the SVD file is not properly written (using tables) and as
 * such all channel registers are declared and defined separately, while
 * they should have the same declaration for chan 0-11 and for chan 12-15.
 * As a consequence:
 *
 * Register access indexation is defined in the bellowing LU macros
 * Register structure used is 0 for chan 0-11, and 12 for 12-15, as
 * these two subsets behave the same
 */

/* 0-15 unified registers */
#define GPDMA_CxLBAR(x) (0x50+(0x80 * x))
#define GPDMA_CxFCR(x)  (0x5c+(0x80 * x))
#define GPDMA_CxSR(x)   (0x60+(0x80 * x))
#define GPDMA_CxCR(x)   (0x64+(0x80 * x))
#define GPDMA_CxTR1(x)  (0x90+(0x80 * x))
#define GPDMA_CxTR2(x)  (0x94+(0x80 * x))
#define GPDMA_CxLLR(x)  (0xcc+(0x80 * x))
/* existing but differenciated 0-11 vs 12-15 registers */
#define GPDMA_CxBR1(x)  (0x98+(0x80 * x))
/* 12-15 only registers */
#define GPDMA_CxSAR(x)  (0x9c+(0x80 * x))
#define GPDMA_CxDAR(x)  (0xa0+(0x80 * x))
#define GPDMA_CxTR3(x)  (0xa4+(0x80 * x))
#define GPDMA_CxBR2(x)  (0xa8+(0x80 * x))


/**
 * @fn check given channel idle flag
 *
 * return true only if
 */
/*@ requires gpdma1_channel_is_valid(channel); */
static inline bool smt32u5_gpdma_is_channel_idle(uint16_t chanid)
{
    bool is_idle = false;
    stm32_gpdma_desc_t const *desc = stm32_gpdma_get_desc();
    gpdma_c0sr_t const *sr = (gpdma_c0sr_t const *)(desc->base_addr + GPDMA_CxSR(chanid));

    return !!sr->idlef;
}

kstatus_t stm32u5_gpdma_probe(void)
{
    return K_STATUS_OKAY;
}

kstatus_t stm32u5_gpdma_channel_configure(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}

kstatus_t stm32u5_gpdma_channel_suspend(void)
{
    return K_STATUS_OKAY;
}

kstatus_t stm32u5_gpdma_channel_resume(void)
{
    return K_STATUS_OKAY;
}

kstatus_t stm32u5_gpdma_channel_abort(void)
{
    return K_STATUS_OKAY;
}

kstatus_t stm32u5_gpdma_channel_restart(void)
{
    return K_STATUS_OKAY;
}
