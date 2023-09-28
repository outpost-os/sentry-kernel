// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file STM32 GPIO controller driver
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
#include <sentry/drivers/gpio/gpio.h>
#include "gpio_defs.h"

/**
 * @brief .rodata field: list of current platform GPIO ports
 *
 * INFO: This driver can be shared between F4 and U5, as there is few differences
 * (mostly some new registers for TZ support)
 */
static const uint32_t gpio_ports_index[] = {
    GPIOA_BASE_ADDR,
    GPIOB_BASE_ADDR,
    GPIOC_BASE_ADDR,
    GPIOD_BASE_ADDR,
    GPIOE_BASE_ADDR,
    GPIOF_BASE_ADDR,
    GPIOG_BASE_ADDR,
    GPIOH_BASE_ADDR,
    GPIOI_BASE_ADDR,
    GPIOJ_BASE_ADDR,
#if defined(CONFIG_ARCH_MCU_STM32F439) || defined(CONFIG_ARCH_MCU_STM32F429)
    /* only for STM32F42x & STM32F43x */
    GPIOK_BASE_ADDR,
#endif
};
/**
 * @brief number of GPIO controlers in the SoC
 */
#define GPIO_PORTS_NUMBER ARRAY_SIZE(gpio_ports_index)

kstatus_t gpio_probe(void)
{
    kstatus_t status = K_STATUS_OKAY;
    /*
     * at probe time, we reset the GPIO controlers value to their reset state.
     * GPIO A and B have some specific reset values (see RM0090, chap. 8.4.1 and next)
     */
    uint8_t pidx = 0;

    /**
     * TODO: if GPIO controler is locked, a gpio_unlock(gpio_port_id) is required first
     */
    /* resetting GPIO A */
    iowrite32(gpio_ports_index[pidx] + GPIO_MODER_REG, 0xa8000000UL);
    iowrite32(gpio_ports_index[pidx] + GPIO_OTYPER_REG, 0x0UL);
    iowrite32(gpio_ports_index[pidx] + GPIO_OSPEEDR_REG, 0x0c000000UL);
    iowrite32(gpio_ports_index[pidx] + GPIO_PUPDR_REG, 0x64000000UL);
    iowrite32(gpio_ports_index[pidx] + GPIO_ODR_REG, 0x0UL);
    iowrite32(gpio_ports_index[pidx] + GPIO_AFRL_REG, 0x0UL);
    iowrite32(gpio_ports_index[pidx] + GPIO_AFRH_REG, 0x0UL);

    /* resetting GPIO B */
    pidx++;
    iowrite32(gpio_ports_index[pidx] + GPIO_MODER_REG, 0x00000280UL);
    iowrite32(gpio_ports_index[pidx] + GPIO_OTYPER_REG, 0x0UL);
    iowrite32(gpio_ports_index[pidx] + GPIO_OSPEEDR_REG, 0x000000c0UL);
    iowrite32(gpio_ports_index[pidx] + GPIO_PUPDR_REG, 0x00000100UL);
    iowrite32(gpio_ports_index[pidx] + GPIO_ODR_REG, 0x0UL);
    iowrite32(gpio_ports_index[pidx] + GPIO_AFRL_REG, 0x0UL);
    iowrite32(gpio_ports_index[pidx] + GPIO_AFRH_REG, 0x0UL);
    pidx++;
    while (pidx < GPIO_PORTS_NUMBER) {
        iowrite32(gpio_ports_index[pidx] + GPIO_MODER_REG, 0x0UL);
        iowrite32(gpio_ports_index[pidx] + GPIO_OTYPER_REG, 0x0UL);
        iowrite32(gpio_ports_index[pidx] + GPIO_OSPEEDR_REG, 0x0UL);
        iowrite32(gpio_ports_index[pidx] + GPIO_PUPDR_REG, 0x0UL);
        iowrite32(gpio_ports_index[pidx] + GPIO_ODR_REG, 0x0UL);
        iowrite32(gpio_ports_index[pidx] + GPIO_AFRL_REG, 0x0UL);
        iowrite32(gpio_ports_index[pidx] + GPIO_AFRH_REG, 0x0UL);
        pidx++;
    }
    return status;
}

/*@
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
kstatus_t gpio_set_mode(uint8_t gpio_port_id, uint8_t pin, gpio_mode_t mode)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    size_t reg = ioread32(gpio_ports_index[gpio_port_id] + GPIO_MODER_REG);
    /* reset current pin mode bits and set mode value */
    reg &= ~(((1ULL << 2) - 1) << (pin*2));
    reg |= (mode << (pin*2));
    iowrite32(gpio_ports_index[gpio_port_id] + GPIO_MODER_REG, reg);
    return status;
}

/*@
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
kstatus_t gpio_set_type(uint8_t gpio_port_id, uint8_t pin, gpio_type_t type)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    size_t reg = ioread32(gpio_ports_index[gpio_port_id] + GPIO_OTYPER_REG);
    reg |= (type << (pin));
    iowrite32(gpio_ports_index[gpio_port_id] + GPIO_OTYPER_REG, reg);
    return status;
}

/*@
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
kstatus_t gpio_set_af(uint8_t gpio_port_id, uint8_t pin, gpio_af_t af)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    size_t afreg;
    size_t reg;

    if (pin < 8) {
        afreg = gpio_ports_index[gpio_port_id] + GPIO_AFRL_REG;
    } else {
        afreg = gpio_ports_index[gpio_port_id] + GPIO_AFRH_REG;
    }
    reg = ioread32(afreg);
    /* reset current pin mode bits and set mode value */
    reg &= ~(((1ULL << 4) - 1) << (pin*4));
    reg |= (af << ((pin % 8)*4));
    iowrite32(afreg, reg);
    return status;
}

/*@
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
kstatus_t gpio_set_speed(uint8_t gpio_port_id, uint8_t pin, gpio_speed_t speed)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    size_t reg = ioread32(gpio_ports_index[gpio_port_id] + GPIO_OSPEEDR_REG);
    /* reset current pin mode bits and set mode value */
    reg &= ~(((1ULL << 2) - 1) << (pin*2));
    reg |= (speed << (pin*2));
    iowrite32(gpio_ports_index[gpio_port_id] + GPIO_OSPEEDR_REG, reg);
    return status;
}

/*@
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
kstatus_t gpio_set_pull_mode(uint8_t gpio_port_id, uint8_t pin, gpio_pullupd_t pupd)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    size_t reg = ioread32(gpio_ports_index[gpio_port_id] + GPIO_PUPDR_REG);
    /* reset current pin mode bits and set mode value */
    reg &= ~(((1ULL << 2) - 1) << (pin*2));
    reg |= (pupd << (pin*2));
    iowrite32(gpio_ports_index[gpio_port_id] + GPIO_PUPDR_REG, reg);
    return status;
}

/*@
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @ requires \valid(val);
  @*/
kstatus_t gpio_get(uint8_t gpio_port_id, uint8_t pin, bool *val)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
     if (unlikely(val == NULL)) {
        status = K_ERROR_INVPARAM;
     }
     /** FIXME: here, instead of a NULL compatison, a sentry_valid_kernel_data() would
       * be better to start with.
       */
#endif
    size_t reg = ioread32(gpio_ports_index[gpio_port_id] + GPIO_IDR_REG);
    *val = !!(reg & (0x1UL << pin)); /* boolean value normalisation */
    return status;
}

/*@
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
/**
 * @brief set GPIO ODRx bit to 1
 *
 * Done through BSRR register for atomic 1 shot access
 */
kstatus_t gpio_set(uint8_t gpio_port_id, uint8_t pin)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    iowrite32(gpio_ports_index[gpio_port_id] + GPIO_BSRR_REG, (0x1ul << (pin)));
    return status;
}

/*@
  @ requires gpio_port_id <= GPIO_PORTS_NUMBER;
  @ requires pin <= 31;
  @*/
/**
 * @brief reset ODRx bit to 0
 *
 * Done through BSRR register for atomic 1 shot access
 */
kstatus_t gpio_reset(uint8_t gpio_port_id, uint8_t pin)
{
    kstatus_t status = K_STATUS_OKAY;
#if CONFIG_SECU_ENFORCE_FAULT_INJECTION
    /**
     * TODO: if Frama-C already demonstrate that all execution pathes to this functions
     * comply with the function contract, input values must be valid. Although, in
     * case of fault injection that may lead to RoP, formal constracts are no more valid
     */
#endif
    iowrite32(gpio_ports_index[gpio_port_id] + GPIO_BSRR_REG, (0x1ul << (pin+16)));
    return status;
}
