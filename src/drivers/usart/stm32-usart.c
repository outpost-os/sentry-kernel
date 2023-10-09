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

#include <assert.h>
#include <stddef.h>
#include <sentry/ktypes.h>
#include <sentry/arch/asm-cortex-m/layout.h>
#include <sentry/arch/asm-cortex-m/irq_defs.h>
#include <sentry/arch/asm-cortex-m/core.h>
#include <sentry/arch/asm-cortex-m/buses.h>
#include <bsp/drivers/clk/rcc.h>
#include <bsp/drivers/usart/usart.h>
#include <sentry/io.h>
#include "usart_defs.h"


__STATIC_INLINE size_t usart_get_base(void)
{
    /* the effective controller to probe is under the control of the Kconfig
       CONFIG_DEBUG_SERIAL_x flags, and as such do not require any argument.
    */
    size_t usart_base = 0;
#if defined(CONFIG_DEBUG_SERIAL_1)
    usart_base = USART1_BASE_ADDR;
#elif defined(CONFIG_DEBUG_SERIAL_2)
    usart_base = USART2_BASE_ADDR;
#elif defined (CONFIG_DEBUG_SERIAL_3)
    usart_base = USART3_BASE_ADDR;
#else
# error "unknown log usart selected!"
#endif
    /*@ assert usart_base != 0; */
    return usart_base;
}

kstatus_t usart_probe(void)
{
    kstatus_t status = K_STATUS_OKAY;
    /* the effective controller to probe is under the control of the Kconfig
       CONFIG_DEBUG_SERIAL_x flags, and as such do not require any argument.
    */
    size_t usart_base = usart_get_base();
    /* standard 8n1 config is set with 0 value, FIXME: what about TIE interrupt ? */
    iowrite32(usart_base + USART_CR1_REG, 0x0UL);
    /* sandard 8n1 config is set with 0 value in CR2 too */
    iowrite32(usart_base + USART_CR2_REG, 0x0UL);
    /* no smartcard, no IrDA, no DMA, no HW flow ctrl */
    iowrite32(usart_base + USART_CR3_REG, 0x0UL);

    /* Prescaler configuration here */
#if 0
    if (config->set_mask & USART_SET_GUARD_TIME_PS) {
	  /* Prescaler and guard time */
	  set_reg(r_CORTEX_M_USART_GTPR(config->usart), config->guard_time_prescaler, USART_CONFIG_GUARD_TIME_PRESCALER);
    }


	/* Clear necessary bits */
	clear_reg_bits(r_CORTEX_M_USART_SR(config->usart), USART_SR_TC_Msk);
	clear_reg_bits(r_CORTEX_M_USART_SR(config->usart), USART_SR_RXNE_Msk);
	clear_reg_bits(r_CORTEX_M_USART_SR(config->usart), USART_SR_CTS_Msk);
	clear_reg_bits(r_CORTEX_M_USART_SR(config->usart), USART_SR_LIN_Msk);
#endif

    return status;
}


/**
 * @brief usart_enable - Enable the USART
 */
kstatus_t usart_enable(void)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t reg;
    size_t usart_base = usart_get_base();
    reg = ioread32(usart_base + USART_CR1_REG);
    reg |= USART_CR1_UE;
    iowrite32(usart_base + USART_CR1_REG, reg);
	return status;
}


/**
 * @brief usart_disable - Disable the USART
 */
kstatus_t usart_disable(void)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t reg;
    size_t usart_base = usart_get_base();
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
 *                      f CK
 * Tx/Rx baud = ------------------------------
 *               8 × ( 2 – OVER8 ) × USARTDIV
 */
kstatus_t usart_set_baudrate(void)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t usart_base = usart_get_base();
    uint32_t divider;
    size_t mantissa;
    size_t fraction;
    size_t reg = 0;
    /* Compute the divider using the baudrate and the APB bus clock
     * (APB1 or APB2) depending on the considered USART */
    size_t over8 = (ioread32(usart_base + USART_CR1_REG) & USART_CR1_OVER8) >> 0xfUL;
    /* over8 is set at 0 at probe time, yet we get it for calculation for genericity */

    /* FIXME: BUS_APB1 is hardcoded here, but should be dtsi-based instead */
    if (unlikely((status = rcc_get_bus_clock(BUS_APB1, &divider)) != K_STATUS_OKAY)) {
        goto err;
    }
    divider /= 115200UL;
    if (unlikely(over8 == 1)) {
        mantissa = (uint16_t) divider >> 3;
        fraction = (uint8_t) ((divider - mantissa * 16));
    } else {
        mantissa = (uint16_t) divider >> 4;
        fraction = (uint8_t) ((divider - mantissa * 8));
    }
    reg |= ((fraction << USART_BRR_DIV_FRACTION_SHIFT) & USART_BRR_DIV_FRACTION_MASK);
    reg |= ((mantissa << USART_BRR_DIV_MANTISSA_SHIFT) & USART_BRR_DIV_MANTISSA_MASK);
    iowrite32(usart_base + USART_BRR_REG, reg);
err:
    return status;
}

/**
 * @brief sending data over USART
 */
kstatus_t usart_tx(uint8_t *data, size_t data_len)
{
    kstatus_t status = K_STATUS_OKAY;
    size_t usart_base = usart_get_base();
    size_t reg;
    usart_enable();
    /* M bit to 0 for 8 bits word length, nothing to do */
    /* stop bits to 1 by default, nothing to do */
    usart_set_baudrate();
    /* set TE bit (transmission enable) */
    reg = ioread32(usart_base + USART_CR1_REG);
    reg |= 1UL << USART_CR1_TE;
    size_t emitted = 0;
    /* transmission loop */
    do {
        iowrite32(usart_base + USART_DR_REG, data[emitted]);
        /* wait for push to shift register. Status cleared by next write */
        do {
            asm volatile("nop":::);
        } while ((ioread32(usart_base + USART_SR_REG) & USART_SR_TXE) == 0);
        emitted++;
    } while (emitted < data_len);
    /* wait for transmission complete (including s)*/
    do {
        asm volatile("nop":::);
    } while ((ioread32(usart_base + USART_SR_REG) & USART_SR_TC) == 0);

    usart_disable();
    return status;
}
