# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

jinja_gen = generator(jinja_cli,
       output: '@BASENAME@',
       arguments: ['-d', '@0@'.format(svd_json),
                   '-o', '@OUTPUT@',
                   '@EXTRA_ARGS@',
                   '@INPUT@'],
       depends: [ svd_json ])


subdir('clk')
subdir('exti')
subdir('flash')
subdir('gpio')

# TODO w/ kconfig driver selector
# no rng IP for stm32f401
if kconfig_data.get('CONFIG_ARCH_MCU_STM32F401', 1) == 0
subdir('rng')
endif

subdir('syscfg')
