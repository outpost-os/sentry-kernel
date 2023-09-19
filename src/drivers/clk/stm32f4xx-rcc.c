// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file STM32F3xx and F4xx PLL & clock driver (see ST RM0090 datasheet)
 */

#include <sentry/arch/asm-cortex-m/soc.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/io.h>
#include <sentry/bits.h>

/* local includes, only manipulated by the driver itself */
#include <sentry/clk.h>

/* RCC generated header for current platform */
#include "rcc_defs.h"
#include "pwr_defs.h"


#define RCC_OSCILLATOR_STABLE	(0)

#define HSE_STARTUP_TIMEOUT	(0x0500UL)
#define HSI_STARTUP_TIMEOUT	(0x0500UL)


#define PROD_CLOCK_APB1  42000000 // Hz
#define PROD_CLOCK_APB2  84000000 // Hz

#define PROD_CORE_FREQUENCY 168000 // KHz


//#include "soc-flash.h"
//#include "m4-cpu.h"

uint64_t clk_get_core_frequency(void)
{
    return (PROD_CORE_FREQUENCY*1000);
}

/*
 * TODO: some of the bellowing code should be M4 generic. Yet, check if all
 * these registers are M4 generic or STM32F4 core specific
 */
void clk_reset(void)
{
    size_t reg;
    /* Reset the RCC clock configuration to the default reset state */
    /* Set HSION bit */
    reg = ioread32(RCC_BASE_ADDR + RCC_CR_REG);
    reg |= BITFIELD_PUT(0x1, RCC_CR_HSION);
    iowrite32(RCC_BASE_ADDR + RCC_CR_REG, reg);

    /* Reset CFGR register */
    iowrite32(RCC_BASE_ADDR + RCC_CFGR_REG, 0x0UL);

    /* Reset HSEON, CSSON and PLLON bits */
    reg = ioread32(RCC_BASE_ADDR + RCC_CR_REG);
    reg &= ~ (RCC_CR_HSEON | RCC_CR_CSSON | RCC_CR_PLLON);
    iowrite32(RCC_BASE_ADDR + RCC_CR_REG, reg);

    /* Reset PLLCFGR register, 0x24.00.30.10 being the reset value */
    iowrite32(RCC_PLLCFGR_REG, 0x24003010UL);

    /* Reset HSEBYP bit */
    reg = ioread32(RCC_BASE_ADDR + RCC_CR_REG);
    reg &= ~(RCC_CR_HSEBYP);
    iowrite32(RCC_BASE_ADDR + RCC_CR_REG, reg);

    /* Reset all interrupts */
    iowrite32(RCC_BASE_ADDR + RCC_CIR_REG, 0x0UL);
}

void clk_set_system_clk(bool enable_hse, bool enable_pll)
{
    uint32_t StartUpCounter = 0;
    size_t reg;

    /*
     * PLL (clocked by HSE/HSI) used as System clock source
     */

    if (enable_hse) {
        /* Enable HSE */
        reg = ioread32(RCC_BASE_ADDR + RCC_CR_REG);
        reg |= RCC_CR_HSEON;
        iowrite32(RCC_BASE_ADDR + RCC_CR_REG, reg);
        do {
            reg = ioread32(RCC_BASE_ADDR + RCC_CR_REG);
            reg &= RCC_CR_HSERDY;
            StartUpCounter++;
        } while ((reg == 0) && (StartUpCounter != HSE_STARTUP_TIMEOUT));
    } else {
        /* Enable HSI */
        reg = ioread32(RCC_BASE_ADDR + RCC_CR_REG);
        reg |= RCC_CR_HSION;
        iowrite32(RCC_BASE_ADDR + RCC_CR_REG, reg);
        do {
            reg = ioread32(RCC_BASE_ADDR + RCC_CR_REG);
            reg &= RCC_CR_HSIRDY;
            StartUpCounter++;
        } while ((reg == 0) && (StartUpCounter != HSI_STARTUP_TIMEOUT));
    }

    if (reg == 0) {
        /* HSE or HSI oscillator is not stable at the end of the timeout window,
         * we should do something
         */
        goto err;
    }

    /* Enable high performance mode, System frequency up to 168 MHz */
    reg = ioread32(RCC_BASE_ADDR + RCC_APB1ENR_REG);
    reg |= RCC_APB1ENR_PWREN;
    iowrite32(RCC_BASE_ADDR + RCC_APB1ENR_REG, reg);
    /*
     * This bit controls the main internal voltage regulator output
     * voltage to achieve a trade-off between performance and power
     * consumption when the device does not operate at the maximum
     * frequency. (DocID018909 Rev 15 - page 141)
     * PWR_CR_VOS = 1 => Scale 1 mode (default value at reset)
     */
    reg = ioread32(PWR_BASE_ADDR + PWR_CR_REG);
    reg |= PWR_CR_VOS_MASK;
    iowrite32(RCC_BASE_ADDR + PWR_CR_REG, reg);


    /* Set clock dividers */
    rcc_cfgr_t cfgr;
    cfgr = (rcc_cfgr_t)ioread32(RCC_BASE_ADDR + RCC_CFGR_REG);
    cfgr.hpre = 0x0; /* nit divide */
    cfgr.ppre1 = 0x5; /* div 4 */
    cfgr.ppre2 = 0x4; /* div 2 */
    iowrite32(RCC_BASE_ADDR + RCC_CFGR_REG, (uint32_t)cfgr);

    if (enable_pll) {
        /* Configure the main PLL */
        /**
         * FIXME: this is the configuration valuses used for Wookey project that
         * are hardcoded, allowing correct (but maybe not optimal) calculation for
         * for various AHB/APB devices. To be checked and properly calculated
         */
        rcc_pllcfgr_t pllcfgr = 0;
        pllcfgr.pllm4 = 1; /* PROD_PLL_M = 16 */
        pllcfgr.pllp1 = 1; /* PROD_PLL_P = 2 */
        pllcfgr.pllq0 = 1; /* PROD_PLL_Q = 7*/
        pllcfgr.pllq1 = 1;
        pllcfgr.pllq2 = 1;
        if (enable_hse) {
            pllcfgr.pllsrc = 1;
        }
        iowrite32(RCC_BASE_ADDR + RCC_PLLCFGR_REG, (uint32_t)pllcfgr);

        reg = ioread32(RCC_BASE_ADDR + RCC_CR_REG);
        reg |= BITFIELD_PUT(0x1ul, RCC_CR_PLLON);
        /* Enable the main PLL */
        iowrite32(RCC_BASE_ADDR + RCC_CR_REG, reg);
        /* Wait till the main PLL is ready */
        while ((ioread32(RCC_BASE_ADDR + RCC_CR_REG) & RCC_CR_PLLRDY) == 0) {
            continue;
        }

        /* Select the main PLL as system clock source */
        reg = ioread32(RCC_BASE_ADDR + RCC_CFGR_REG);
        reg &= ~RCC_CFGR_SW;
        reg |= BITFIELD_PUT(RCC_CFGR_SW_PLL, RCC_CFGR_SW);
        iowrite32(RCC_BASE_ADDR + RCC_CFGR_REG, reg);

        /* Wait till the main PLL is used as system clock source */
        while (BITFIELD_GET(ioread32(RCC_BASE_ADDR + RCC_CFGR_REG), RCC_CFGR_SWS) != RCC_CFGR_SWS_PLL) {
            continue;
        }
    }

#if 0
    /* Configure Flash prefetch, Instruction cache, Data cache and wait state */
    write_reg_value(FLASH_ACR, FLASH_ACR_ICEN
                    | FLASH_ACR_DCEN | FLASH_ACR_LATENCY_5WS);
#endif

    return;
err:
    return;
    //panic();
}
