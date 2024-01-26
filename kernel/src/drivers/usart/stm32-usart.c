// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file STM32 USART block lightweight support for logging (Tx) only
 * Only if kernel built in debug mode and UART identifier selected
 *
 * As this is a simple debugging usart, this driver is made to support
 * only the usage 8bits word, 1 start bit, n stop bit (8n1) configuration.
 * As a consequence, usart_rx and usart_tx manipuate uint8_t data only.
 */

#include <stddef.h>
#include <sentry/ktypes.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/arch/asm-cortex-m/irq_defs.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/arch/asm-cortex-m/buses.h>
#include <sentry/managers/memory.h>
#include <bsp/drivers/clk/rcc.h>
#include <bsp/drivers/usart/usart.h>
#include <bsp/drivers/gpio/gpio.h>
#include <sentry/io.h>
#include "usart_defs.h"
#include "stm32-usart-dt.h"

#if defined(CONFIG_SOC_SUBFAMILY_STM32L4)
/* STM32L4 family USART registers are slightly different but we can have an
 * an homogeneous driver thanks to the simplicity of our usage at kernel level
 */
#define USART_SR_REG USART_ISR_REG
#define USART_SR_TXE USART_ISR_TXE
#define USART_SR_TC  USART_ISR_TC
/* receive & transmit registers separated. We only use transmit in kernel */
#define USART_DR_REG USART_TDR_REG

#elif defined(CONFIG_SOC_SUBFAMILY_STM32U5)
#define USART_SR_REG USART_ISR_DISABLED_REG
#define USART_SR_TXE USART_ISR_DISABLED_TXFNF
#define USART_SR_TC  USART_ISR_DISABLED_TC

#define USART_CR1_REG USART_CR1_DISABLED_REG
#define USART_CR1_UE USART_CR1_DISABLED_UE
#define USART_CR1_TE USART_CR1_DISABLED_TE
#define USART_CR1_OVER8_SHIFT USART_CR1_DISABLED_OVER8_SHIFT
#define USART_CR1_OVER8_MASK USART_CR1_DISABLED_OVER8_MASK
/* receive & transmit registers separated. We only use transmit in kernel */
#define USART_DR_REG USART_TDR_REG
#endif



static inline kstatus_t usart_map(void)
{
    stm32_usartport_desc_t const * usart_desc = stm32_usartport_get_desc();
    return mgr_mm_map_kdev(usart_desc->base_addr, usart_desc->size);
}
/* for simplicity sake, but unmaping a kernel device is generic */
static inline kstatus_t usart_unmap(void) {
    return mgr_mm_unmap_kdev();
}

static kstatus_t usart_set_baudrate(void);

kstatus_t usart_probe(void)
{
    kstatus_t status = K_STATUS_OKAY;
    stm32_usartport_desc_t const * usart_desc = stm32_usartport_get_desc();
    size_t pin;
    size_t usart_base = usart_desc->base_addr;

    /* other IPs mapping is under other IP responsability */
    rcc_enable(usart_desc->bus_id, usart_desc->clk_msk, RCC_NOFLAG);
    for (pin = 0; pin < usart_desc->pinctrl_tbl_size; pin++) {
        status = gpio_pinctrl_configure(usart_desc->pinctrl_tbl[pin]);
        if (unlikely(status != K_STATUS_OKAY)) {
            goto err;
        }
    }
    /* map usart before manipulating it */
    if (unlikely((status = usart_map()) != K_STATUS_OKAY)) {
        goto err;
    }
    /* standard 8n1 config is set with 0 value, FIXME: what about TIE interrupt ? */
    iowrite32(usart_base + USART_CR1_REG, 0x0UL);
    /* sandard 8n1 config is set with 0 value in CR2 too */
    iowrite32(usart_base + USART_CR2_REG, 0x0UL);
    /* no smartcard, no IrDA, no DMA, no HW flow ctrl */
    iowrite32(usart_base + USART_CR3_REG, 0x0UL);

    usart_unmap();

err:
    return status;
}

/**
 * @brief usart_enable - Enable the USART
 */
static kstatus_t usart_enable(void)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t reg;
    stm32_usartport_desc_t const *usart_desc = stm32_usartport_get_desc();
    size_t usart_base = usart_desc->base_addr;

    reg = ioread32(usart_base + USART_CR1_REG);
    reg |= USART_CR1_UE;
    iowrite32(usart_base + USART_CR1_REG, reg);
	return status;
}

/**
 * @brief usart_disable - Disable the USART
 */
static kstatus_t usart_disable(void)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t reg;
    stm32_usartport_desc_t const *usart_desc = stm32_usartport_get_desc();
    size_t usart_base = usart_desc->base_addr;
    reg = ioread32(usart_base + USART_CR1_REG);
    reg &= ~USART_CR1_UE;
    iowrite32(usart_base + USART_CR1_REG, reg);
	return status;
}

/**
 * @brief set USART baudrate to 115.200 bps
 *
 * No argument here, we fix the Baudrate to 115.200 bps
 *
 * In Standard USART mode (i.e. neither IrDA nor Smartcard mode),
 * the baudrate is calculated with the following function:
 *
 * STM32F4 family:
 *                      f CK
 * Tx/Rx baud = ------------------------------
 *               8 × ( 2 – OVER8 ) × USARTDIV
 */
static kstatus_t usart_set_baudrate(void)
{
    kstatus_t status = K_STATUS_OKAY;
    stm32_usartport_desc_t const *usart_desc = stm32_usartport_get_desc();
    size_t usart_base = usart_desc->base_addr;
    uint32_t uart_clk;
    uint32_t brr;
    uint32_t usartdiv;
    /* Compute the divider using the baudrate and the APB bus clock
     * (APB1 or APB2) depending on the considered USART */
    size_t over8 = (ioread32(usart_base + USART_CR1_REG) & USART_CR1_OVER8_MASK) >> USART_CR1_OVER8_SHIFT;
    /* over8 is set at 0 at probe time, yet we get it for calculation for genericity */

    /*
     * FIXME: BUS_APB1 is hardcoded here, but should be dtsi-based instead
     * FIXME: For STM32U5, this is not hte peripheral bus clock but the usart kernel clock (which is PCLKx by default)
     */
    if (unlikely((status = rcc_get_bus_clock(usart_desc->bus_id, &uart_clk)) != K_STATUS_OKAY)) {
        goto err;
    }

    usartdiv = DIV_ROUND_UP(uart_clk, 115200);
    brr = usartdiv & 0xfff0UL;
    brr |= (usartdiv >> over8) & 0xfUL;

    iowrite32(usart_base + USART_BRR_REG, brr);
err:
    return status;
}


/**
 * @brief sending data over USART
 */
/*@
  requires \valid_read(data + (0 .. data_len-1));
  requires data_len > 0;
*/
kstatus_t usart_tx(const uint8_t *data, size_t data_len)
{
    kstatus_t status = K_STATUS_OKAY;
    stm32_usartport_desc_t const *usart_desc = stm32_usartport_get_desc();
    size_t usart_base = usart_desc->base_addr;
    size_t reg;

    if (unlikely((status = usart_map()) != K_STATUS_OKAY)) {
        goto err;
    }
    usart_set_baudrate();
    usart_enable();

    /* M bit to 0 for 8 bits word length, nothing to do */
    /* stop bits to 1 by default, nothing to do */

    /* set TE bit (transmission enable) */
    reg = ioread32(usart_base + USART_CR1_REG);
    reg |= USART_CR1_TE;
    iowrite32(usart_base + USART_CR1_REG, reg);
    size_t emitted = 0;
    /* transmission loop */
    do {
        do {
            asm volatile("nop":::);
        } while ((ioread32(usart_base + USART_SR_REG) & USART_SR_TXE) == 0);
        iowrite32(usart_base + USART_DR_REG, data[emitted]);
        /* wait for push to shift register. Status cleared by next write */
        emitted++;
    } while (emitted < data_len);
    /* wait for transmission complete (including s)*/
    do {
        asm volatile("nop":::);
    } while ((ioread32(usart_base + USART_SR_REG) & USART_SR_TC) == 0);

    usart_disable();
    status = usart_unmap();
err:
    return status;
}
