# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# list of statically defined headers
sentry_header_set.add(files(
    'flash/flash.h',
    'gpio/gpio.h',
    'gpio/pinctrl.h',
    'rng/rng.h',
    'clk/rcc.h',
    'clk/pwr.h',
    'exti/exti.h',
    'syscfg/syscfg.h',
))

# FIXME:
# Those might not be exposed here but htere is a limitation w/ meson generator
# as generated files may consume driver header
sentry_header_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32F4', if_true: files('clk/stm32x4-pll.h'))
sentry_header_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32L4', if_true: files('clk/stm32x4-pll.h'))
