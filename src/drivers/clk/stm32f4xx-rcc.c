// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file STM32F3xx and F4xx PLL & clock driver (see ST RM0090 datasheet)
 */

#include <sentry/arch/asm-cortex-m/soc.h>
#include <sentry/io.h>
#include <sentry/bits.h>

/* local includes, only manipulated by the driver itself */
#include <sentry/clk.h>
#include "stm32f4xx-pwr.h"

#define RCC_BASE (AHB1PERIPH_BASE + 0x3800UL)

/* RCC main control register */
#define  RCC_CR                 (RCC_BASE + 0x00UL)

#define  RCC_CR_HSION           BIT(0)
#define  RCC_CR_HSIRDY          BIT(1)
#define  RCC_CR_HSITRIM         BITFIELD_MASK(7, 3)
#define  RCC_CR_HSICAL          BITFIELD_MASK(15, 8)
#define  RCC_CR_HSEON           BIT(16)
#define  RCC_CR_HSERDY          BIT(17)
#define  RCC_CR_HSEBYP          BIT(18)
#define  RCC_CR_CSSON           BIT(19)
#define  RCC_CR_PLLON           BIT(24)
#define  RCC_CR_PLLRDY          BIT(25)
#define  RCC_CR_PLLI2SON        BIT(26)
#define  RCC_CR_PLLI2SRDY       BIT(27)
#define  RCC_CR_PLLSAION        BIT(28)
#define  RCC_CR_PLLSAIRDY       BIT(29)

/* PLL configuration register */
#define RCC_PLLCFGR             (RCC_BASE + 0x04UL)

#define RCC_PLLCFGR_PLLM        BITFIELD_MASK(5, 0)
#define RCC_PLLCFGR_PLLN        BITFIELD_MASK(14, 6)
#define RCC_PLLCFGR_PLLP        BITFIELD_MASK(17, 16)
#define RCC_PLLCFGR_PLLSRC      BIT(22) /* 0 == HSI, 1 == HSE */

#define RCC_PLLCFGR_PLLSRC_HSE  (0x1UL)
#define RCC_PLLCFGR_PLLSRC_HSI  (0x0UL)

#define RCC_PLLCFGR_PLLQ        BITFIELD_MASK(27, 24)
#define RCC_CFGR                (RCC_BASE + 0x08UL)
#define  RCC_CFGR_SW            BITFIELD_MASK(1, 0)    /* System clock Switch */
#define  RCC_CFGR_SW_HSI        (0x0UL)    /* HSI selected as system clock */
#define  RCC_CFGR_SW_HSE        (0x1UL)    /* HSE selected as system clock */
#define  RCC_CFGR_SW_PLL        (0x2UL)    /* PLL selected as system clock */
#define  RCC_CFGR_SWS           BITFIELD_MASK(3, 2)    /* System Clock Switch Status */
#define  RCC_CFGR_SWS_HSI       (0x0UL)    /* HSI oscillator used as system clock */
#define  RCC_CFGR_SWS_HSE       (0x1UL)    /* HSE oscillator used as system clock */
#define  RCC_CFGR_SWS_PLL       (0x2UL)    /* PLL used as system clock */
#define  RCC_CFGR_HPRE          BITFIELD_MASK(7, 4)    /* AHB prescaler */
#define  RCC_CFGR_HPRE_DIV1     (0x0UL)    /* SYSCLK not divided */
#define  RCC_CFGR_HPRE_DIV2     (0x8UL)    /* SYSCLK divided by 2 */
#define  RCC_CFGR_HPRE_DIV4     (0x9UL)    /* SYSCLK divided by 4 */
#define  RCC_CFGR_HPRE_DIV8     (0xaUL)    /* SYSCLK divided by 8 */
#define  RCC_CFGR_HPRE_DIV16    (0xbUL)    /* SYSCLK divided by 16 */
#define  RCC_CFGR_HPRE_DIV64    (0xcUL)    /* SYSCLK divided by 64 */
#define  RCC_CFGR_HPRE_DIV128   (0xdUL)    /* SYSCLK divided by 128 */
#define  RCC_CFGR_HPRE_DIV256   (0xeUL)    /* SYSCLK divided by 256 */
#define  RCC_CFGR_HPRE_DIV512   (0xfUL)    /* SYSCLK divided by 512 */
#define  RCC_CFGR_PPRE1         BITFIELD_MASK(12, 10)    /* APB1 prescaler */
#define  RCC_CFGR_PPRE1_DIV1    (0x0UL)    /* HCLK not divided */
#define  RCC_CFGR_PPRE1_DIV2    (0x4UL)    /* HCLK divided by 2 */
#define  RCC_CFGR_PPRE1_DIV4    (0x5UL)    /* HCLK divided by 4 */
#define  RCC_CFGR_PPRE1_DIV8    (0x6UL)    /* HCLK divided by 8 */
#define  RCC_CFGR_HPRE1_DIV16   (0x7UL)    /* HCLK divided by 16 */
#define  RCC_CFGR_PPRE2         BITFIELD_MASK(15, 13)    /* APB2 prescaler */
#define  RCC_CFGR_HPRE2_DIV1    (0x0UL)    /* HCLK not divided */
#define  RCC_CFGR_HPRE2_DIV2    (0x4UL)    /* HCLK divided by 2 */
#define  RCC_CFGR_HPRE2_DIV4    (0x5UL)    /* HCLK divided by 4 */
#define  RCC_CFGR_HPRE2_DIV8    (0x6UL)    /* HCLK divided by 8 */
#define  RCC_CFGR_HPRE2_DIV16   (0x7UL)    /* HCLK divided by 16 */
#define  RCC_CFGR_RTCPRE        BITFIELD_MASK(20, 16)
#define  RCC_CFGR_MCO1          BITFIELD_MASK(22, 21)
#define  RCC_CFGR_I2SSRC        BIT(23)
#define  RCC_CFGR_MCO1PRE       BITFIELD_MASK(26, 24)
#define  RCC_CFGR_MCO2PRE       BITFIELD_MASK(29, 27)
#define  RCC_CFGR_MCO2          BITFIELD_MASK(31, 30)

/* RCC clock interrupt register (RCC_CIRUL) */
#define RCC_CIR                 (RCC_BASE + 0x0CUL)

#define  RCC_CIR_LSIRDYF        BIT(0)
#define  RCC_CIR_LSERDYF        BIT(1)
#define  RCC_CIR_HSIRDYF        BIT(2)
#define  RCC_CIR_HSERDYF        BIT(3)
#define  RCC_CIR_PLLRDYF        BIT(4)
#define  RCC_CIR_PLLI2SRDYF     BIT(5)
#define  RCC_CIR_PLLSAIRDYF     BIT(6)
#define  RCC_CIR_CSSF           BIT(7)
#define  RCC_CIR_LSIRDYIE       BIT(8)
#define  RCC_CIR_LSERDYIE       BIT(9)
#define  RCC_CIR_HSIRDYIE       BIT(10)
#define  RCC_CIR_HSERDYIE       BIT(11)
#define  RCC_CIR_PLLRDYIE       BIT(12)
#define  RCC_CIR_PLLI2SRDYIE    BIT(13)
#define  RCC_CIR_PLLSAIRDYIE    BIT(14)
#define  RCC_CIR_LSIRDYC        BIT(16)
#define  RCC_CIR_LSERDYC        BIT(17)
#define  RCC_CIR_HSIRDYC        BIT(18)
#define  RCC_CIR_HSERDYC        BIT(19)
#define  RCC_CIR_PLLRDYC        BIT(20)
#define  RCC_CIR_PLLI2SRDYC     BIT(21)
#define  RCC_CIR_PLLSAIRDYC     BIT(22)
#define  RCC_CIR_CSSC           BIT(23)

/* AHB1 Peripheral reset register */
#define RCC_AHB1RSTR            (RCC_BASE + 0x10UL)

#define  RCC_AHB1RSTR_GPIOARST  BIT(0)
#define  RCC_AHB1RSTR_GPIOBRST  BIT(1)
#define  RCC_AHB1RSTR_GPIOCRST  BIT(2)
#define  RCC_AHB1RSTR_GPIODRST  BIT(3)
#define  RCC_AHB1RSTR_GPIOERST  BIT(4)
#define  RCC_AHB1RSTR_GPIOFRST  BIT(5)
#define  RCC_AHB1RSTR_GPIOGRST  BIT(6)
#define  RCC_AHB1RSTR_GPIOHRST  BIT(7)
#define  RCC_AHB1RSTR_GPIOIRST  BIT(8)
#define  RCC_AHB1RSTR_GPIOJRST  BIT(9)
#define  RCC_AHB1RSTR_GPIOKRST  BIT(10)
#define  RCC_AHB1RSTR_CRCRST    BIT(12)
#define  RCC_AHB1RSTR_DMA1RST   BIT(21)
#define  RCC_AHB1RSTR_DMA2RST   BIT(22)
#define  RCC_AHB1RSTR_DMA2DRST  BIT(23)
#define  RCC_AHB1RSTR_ETHMACRST BIT(25)
#define  RCC_AHB1RSTR_OTGHRST   BIT(29)

/* AHB2 Peripheral reset register */
#define RCC_AHB2RSTR            (RCC_BASE + 0x14UL)

#define  RCC_AHB2RSTR_DCMIRST   BIT(0)
#define  RCC_AHB2RSTR_CRYPRST   BIT(4)
#define  RCC_AHB2RSTR_HSAHRST   BIT(5)
#define  RCC_AHB2RSTR_RNGRST    BIT(6)
#define  RCC_AHB2RSTR_OTGFSRST  BIT(7)

/* AHB3 Peripheral reset register */
#define RCC_AHB3RSTR            (RCC_BASE + 0x18UL)

#define  RCC_AHB3RSTR_FSMCRST   BIT(0)

/* APB1 Peripheral reset register */
#define RCC_APB1RSTR     (RCC_BASE + 0x20UL)

#define RCC_APB1RSTR_TIM2RST    BIT(0)
#define RCC_APB1RSTR_TIM3RST    BIT(1)
#define RCC_APB1RSTR_TIM4RST    BIT(2)
#define RCC_APB1RSTR_TIM5RST    BIT(3)
#define RCC_APB1RSTR_TIM6RST    BIT(4)
#define RCC_APB1RSTR_TIM7RST    BIT(5)
#define RCC_APB1RSTR_TIM12RST   BIT(6)
#define RCC_APB1RSTR_TIM13RST   BIT(7)
#define RCC_APB1RSTR_TIM14RST   BIT(8)
#define RCC_APB1RSTR_WWDGRST    BIT(11)
#define RCC_APB1RSTR_SPI2RST    BIT(14)
#define RCC_APB1RSTR_SPI3RST    BIT(15)
#define RCC_APB1RSTR_UART2RST   BIT(17)
#define RCC_APB1RSTR_UART3RST   BIT(18)
#define RCC_APB1RSTR_UART4RST   BIT(19)
#define RCC_APB1RSTR_UART5RST   BIT(20)
#define RCC_APB1RSTR_I2C1RST    BIT(21)
#define RCC_APB1RSTR_I2C2RST    BIT(22)
#define RCC_APB1RSTR_I2C3RST    BIT(23)
#define RCC_APB1RSTR_CAN1RST    BIT(25)
#define RCC_APB1RSTR_CAN2RST    BIT(26)
#define RCC_APB1RSTR_PWRRST     BIT(28)
#define RCC_APB1RSTR_DACRST     BIT(29)
#define RCC_APB1RSTR_UART7RST   BIT(30)
#define RCC_APB1RSTR_UART8RST   BIT(31)

/* APB2 Peripheral reset register */
#define RCC_APB2RSTR            (RCC_BASE + 0x24UL)

#define RCC_APB2RSTR_TIM1RST    BIT(0)
#define RCC_APB2RSTR_TIM8RST    BIT(1)
#define RCC_APB2RSTR_USART1RST  BIT(4)
#define RCC_APB2RSTR_USART6RST  BIT(5)
#define RCC_APB2RSTR_ADCRST     BIT(8)
#define RCC_APB2RSTR_SDIORST    BIT(11)
#define RCC_APB2RSTR_SPI1RST    BIT(12)
#define RCC_APB2RSTR_SPI4RST    BIT(13)
#define RCC_APB2RSTR_SYSCFGRST  BIT(14)
#define RCC_APB2RSTR_TIM9RST    BIT(16)
#define RCC_APB2RSTR_TIM10RST   BIT(17)
#define RCC_APB2RSTR_TIM11RST   BIT(18)
#define RCC_APB2RSTR_SPI5RST    BIT(20)
#define RCC_APB2RSTR_SPI6RST    BIT(21)
#define RCC_APB2RSTR_SAI1RST    BIT(22)
#define RCC_APB2RSTR_LTDCRST    BIT(26)

/*
 * All fields of RST registers are mapped in the same way in the
 * Enable regisers. Although there is some enable bits that do
 * not exist in the reset registers
 */

/* AHB1 Peripheral enable register */
#define RCC_AHB1ENR      (RCC_BASE + 0x30UL)

#define  RCC_AHB1ENR_GPIOAEN      BIT(0)
#define  RCC_AHB1ENR_GPIOBEN      BIT(1)
#define  RCC_AHB1ENR_GPIOCEN      BIT(2)
#define  RCC_AHB1ENR_GPIODEN      BIT(3)
#define  RCC_AHB1ENR_GPIOEEN      BIT(4)
#define  RCC_AHB1ENR_GPIOFEN      BIT(5)
#define  RCC_AHB1ENR_GPIOGEN      BIT(6)
#define  RCC_AHB1ENR_GPIOHEN      BIT(7)
#define  RCC_AHB1ENR_GPIOIEN      BIT(8)
#define  RCC_AHB1ENR_GPIOJEN      BIT(9)
#define  RCC_AHB1ENR_GPIOKEN      BIT(10)
#define  RCC_AHB1ENR_CRCEN        BIT(12)
#define  RCC_AHB1ENR_BKPSRAMEN    BIT(18)
#define  RCC_AHB1ENR_CCMDATARAMEN BIT(20)
#define  RCC_AHB1ENR_DMA1EN       BIT(21)
#define  RCC_AHB1ENR_DMA2EN       BIT(22)
#define  RCC_AHB1ENR_DMA2DEN      BIT(23)
#define  RCC_AHB1ENR_ETHMACEN     BIT(25)
#define  RCC_AHB1ENR_ETHMACTXEN   BIT(26)
#define  RCC_AHB1ENR_ETHMACRXEN   BIT(27)
#define  RCC_AHB1ENR_ETHMACPTPEN  BIT(28)
#define  RCC_AHB1RSTR_OTGHEN      BIT(29)
#define  RCC_AHB1RSTR_OTGHULPIEN  BIT(30)

/* AHB2 Peripheral enable register */
#define RCC_AHB2ENR      (RCC_BASE + 0x34UL)

#define  RCC_AHB2ENR_DCMIEN      BIT(0)
#define  RCC_AHB2ENR_CRYPEN      BIT(4)
#define  RCC_AHB2ENR_HSAHEN      BIT(5)
#define  RCC_AHB2ENR_RNGEN       BIT(6)
#define  RCC_AHB2ENR_OTGFSEN     BIT(7)

/* AHB3 Peripheral enable register */
#define RCC_AHB3ENR      (RCC_BASE + 0x38UL)

#define  RCC_AHB3ENR_FSMCEN   BIT(0)

/* APB1 Peripheral enable register */
#define RCC_APB1ENR      (RCC_BASE + 0x40UL)

#define RCC_APB1ENR_TIM2EN    BIT(0)
#define RCC_APB1ENR_TIM3EN    BIT(1)
#define RCC_APB1ENR_TIM4EN    BIT(2)
#define RCC_APB1ENR_TIM5EN    BIT(3)
#define RCC_APB1ENR_TIM6EN    BIT(4)
#define RCC_APB1ENR_TIM7EN    BIT(5)
#define RCC_APB1ENR_TIM12EN   BIT(6)
#define RCC_APB1ENR_TIM13EN   BIT(7)
#define RCC_APB1ENR_TIM14EN   BIT(8)
#define RCC_APB1ENR_WWDGEN    BIT(11)
#define RCC_APB1ENR_SPI2EN    BIT(14)
#define RCC_APB1ENR_SPI3EN    BIT(15)
#define RCC_APB1ENR_UART2EN   BIT(17)
#define RCC_APB1ENR_UART3EN   BIT(18)
#define RCC_APB1ENR_UART4EN   BIT(19)
#define RCC_APB1ENR_UART5EN   BIT(20)
#define RCC_APB1ENR_I2C1EN    BIT(21)
#define RCC_APB1ENR_I2C2EN    BIT(22)
#define RCC_APB1ENR_I2C3EN    BIT(23)
#define RCC_APB1ENR_CAN1EN    BIT(25)
#define RCC_APB1ENR_CAN2EN    BIT(26)
#define RCC_APB1ENR_PWREN     BIT(28)
#define RCC_APB1ENR_DACEN     BIT(29)
#define RCC_APB1ENR_UART7EN   BIT(30)
#define RCC_APB1ENR_UART8EN   BIT(31)

/* APB2 Peripheral enable register */
#define RCC_APB2ENR      (RCC_BASE + 0x44UL)

#define RCC_APB2ENR_TIM1EN    BIT(0)
#define RCC_APB2ENR_TIM8EN    BIT(1)
#define RCC_APB2ENR_USART1EN  BIT(4)
#define RCC_APB2ENR_USART6EN  BIT(5)
#define RCC_APB2ENR_ADC1EN    BIT(8)
#define RCC_APB2ENR_ADC2EN    BIT(9)
#define RCC_APB2ENR_ADC3EN    BIT(10)
#define RCC_APB2ENR_SDIOEN    BIT(11)
#define RCC_APB2ENR_SPI1EN    BIT(12)
#define RCC_APB2ENR_SPI4EN    BIT(13)
#define RCC_APB2ENR_SYSCFGEN  BIT(14)
#define RCC_APB2ENR_TIM9EN    BIT(16)
#define RCC_APB2ENR_TIM10EN   BIT(17)
#define RCC_APB2ENR_TIM11EN   BIT(18)
#define RCC_APB2ENR_SPI5EN    BIT(20)
#define RCC_APB2ENR_SPI6EN    BIT(21)
#define RCC_APB2ENR_SAI1EN    BIT(22)
#define RCC_APB2ENR_LTDCEN    BIT(26)

/* low power registers defined but not supported by now */
#define RCC_AHB1LPENR    (RCC_BASE + 0x50UL)
#define RCC_AHB2LPENR    (RCC_BASE + 0x54UL)
#define RCC_AHB3LPENR    (RCC_BASE + 0x58UL)
#define RCC_APB1LPENR    (RCC_BASE + 0x60UL)
#define RCC_APB2LPENR    (RCC_BASE + 0x64UL)

/* Backup domain control register */
#define RCC_BDCR         (RCC_BASE + 0x70UL)

#define RCC_BDCR_LSEON   BIT(0)
#define RCC_BDCR_LSERDY  BIT(1)
#define RCC_BDCR_LSEBYP  BIT(2)
#define RCC_BDCR_RTCSEL  BITFIELD_MASK(9, 8)
#define RCC_BDCR_RTCEN   BIT(15)
#define RCC_BDCR_BDRST   BIT(16)

/* Clock control & status register */
#define RCC_CSR            (RCC_BASE + 0x74UL)

#define  RCC_CSR_LSION     BIT(0)
#define  RCC_CSR_LSIRDY    BIT(1)
#define  RCC_CSR_RMVF      BIT(24)
#define  RCC_CSR_BORRSTF   BIT(25)
#define  RCC_CSR_PADRSTF   BIT(26)
#define  RCC_CSR_PORRSTF   BIT(27)
#define  RCC_CSR_SFTRSTF   BIT(28)
#define  RCC_CSR_WDGRSTF   BIT(29)
#define  RCC_CSR_WWDGRSTF  BIT(30)
#define  RCC_CSR_LPWRRSTF  BIT(31)

/* Spread spectrum clock generation register */
#define RCC_SSCGR        (RCC_BASE + 0x80UL)

#define  RCC_SSCGR_MODPER     BITFIELD_MASK(12, 0)
#define  RCC_SSCGR_INCSTEP    BITFIELD_MASK(27, 13)
#define  RCC_SSCGR_SPREADSEL  BIT(30)
#define  RCC_SSCGR_SSCGEN     BIT(31)

/* PLLI2S configuration register */
#define RCC_PLLI2SCFGR   (RCC_BASE + 0x84UL)
/* PLLSAI Configuration register */
#define RCC_PLLSAICFGR   (RCC_BASE + 0x88UL)
/* Dedicated clock Configuration register */
#define RCC_DCKCFGR      (RCC_BASE + 0x8CUL)


#define RCC_OSCILLATOR_STABLE	(0)

#define HSE_STARTUP_TIMEOUT	(0x0500UL)
#define HSI_STARTUP_TIMEOUT	(0x0500UL)


/**
 * FIXME: this is the configuration valuses used for Wookey project that
 * are hardcoded, allowing correct (but maybe not optimal) calculation for
 * for various AHB/APB devices. To be checked and properly calculated
 */
#define PROD_PLL_M     16
#define PROD_PLL_N     336
#define PROD_PLL_P     2
#define PROD_PLL_Q     7

#define PROD_HCLK      RCC_CFGR_HPRE_DIV1
#define PROD_PCLK2     RCC_CFGR_HPRE2_DIV2
#define PROD_PCLK1     RCC_CFGR_PPRE1_DIV4

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
    reg = ioread32(RCC_CR);
    reg |= BITFIELD_PUT(0x1, RCC_CR_HSION);
    iowrite32(RCC_CR, reg);

    /* Reset CFGR register */
    iowrite32(RCC_CFGR, 0x0UL);

    /* Reset HSEON, CSSON and PLLON bits */
    reg = ioread32(RCC_CR);
    reg &= ~ (RCC_CR_HSEON | RCC_CR_CSSON | RCC_CR_PLLON);
    iowrite32(RCC_CR, reg);

    /* Reset PLLCFGR register, 0x24.00.30.10 being the reset value */
    iowrite32(RCC_PLLCFGR, 0x24003010UL);

    /* Reset HSEBYP bit */
    reg = ioread32(RCC_CR);
    reg &= ~(RCC_CR_HSEBYP);
    iowrite32(RCC_CR, reg);

    /* Reset all interrupts */
    iowrite32(RCC_CIR, 0x0UL);
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
        reg = ioread32(RCC_CR);
        reg |= RCC_CR_HSEON;
        iowrite32(RCC_CR, reg);
        do {
            reg = ioread32(RCC_CR);
            reg &= RCC_CR_HSERDY;
            StartUpCounter++;
        } while ((reg == 0) && (StartUpCounter != HSE_STARTUP_TIMEOUT));
    } else {
        /* Enable HSI */
        reg = ioread32(RCC_CR);
        reg |= RCC_CR_HSION;
        iowrite32(RCC_CR, reg);
        do {
            reg = ioread32(RCC_CR);
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
    reg = ioread32(RCC_APB1ENR);
    reg |= RCC_APB1ENR_PWREN;
    iowrite32(RCC_APB1ENR, reg);
    /*
     * This bit controls the main internal voltage regulator output
     * voltage to achieve a trade-off between performance and power
     * consumption when the device does not operate at the maximum
     * frequency. (DocID018909 Rev 15 - page 141)
     * PWR_CR_VOS = 1 => Scale 1 mode (default value at reset)
     */
    reg = ioread32(PWR_CR);
    reg |= PWR_CR_VOS_Msk;
    iowrite32(PWR_CR, reg);

    /* Set clock dividers */
    ioread32(RCC_CFGR);
    reg |= (PROD_HCLK | PROD_PCLK2 | PROD_PCLK1);
    iowrite32(RCC_CFGR, reg);

    if (enable_pll) {
        /* Configure the main PLL */
        if (enable_hse) {
            reg = BITFIELD_PUT(PROD_PLL_M, RCC_PLLCFGR_PLLM)
                | BITFIELD_PUT(PROD_PLL_N, RCC_PLLCFGR_PLLN)
                | BITFIELD_PUT(((PROD_PLL_P >> 1) - 1), RCC_PLLCFGR_PLLP)
                | BITFIELD_PUT(RCC_PLLCFGR_PLLSRC_HSE, RCC_PLLCFGR_PLLSRC)
                | BITFIELD_PUT(PROD_PLL_Q, RCC_PLLCFGR_PLLQ);
        } else {
            reg = BITFIELD_PUT(PROD_PLL_M, RCC_PLLCFGR_PLLM)
                | BITFIELD_PUT(PROD_PLL_N, RCC_PLLCFGR_PLLN)
                | BITFIELD_PUT(((PROD_PLL_P >> 1) - 1), RCC_PLLCFGR_PLLP)
                | BITFIELD_PUT(RCC_PLLCFGR_PLLSRC_HSI, RCC_PLLCFGR_PLLSRC)
                | BITFIELD_PUT(PROD_PLL_Q, RCC_PLLCFGR_PLLQ);

        }
        iowrite32(RCC_PLLCFGR, reg);

        reg = ioread32(RCC_CR);
        reg |= BITFIELD_PUT(0x1ul, RCC_CR_PLLON);
        /* Enable the main PLL */
        iowrite32(RCC_CR, reg);
        /* Wait till the main PLL is ready */
        while ((ioread32(RCC_CR) & RCC_CR_PLLRDY) == 0) {
            continue;
        }

        /* Select the main PLL as system clock source */
        reg = ioread32(RCC_CFGR);
        reg &= ~RCC_CFGR_SW;
        reg |= BITFIELD_PUT(RCC_CFGR_SW_PLL, RCC_CFGR_SW);
        iowrite32(RCC_CFGR, reg);

        /* Wait till the main PLL is used as system clock source */
        while (BITFIELD_GET(ioread32(RCC_CFGR), RCC_CFGR_SWS) != RCC_CFGR_SWS_PLL) {
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
