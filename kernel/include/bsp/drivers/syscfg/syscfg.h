// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef SYSCFG_H
#define SYSCFG_H

#include <sentry/ktypes.h>

kstatus_t syscfg_probe(void);

#ifdef CONFIG_HAS_FLASH_DUAL_BANK
kstatus_t syscfg_switch_bank(void);
#endif

kstatus_t syscfg_set_exti(uint8_t gpio_pin_id,  uint8_t gpio_port_id);

#endif/*SYSCFG_H*/
