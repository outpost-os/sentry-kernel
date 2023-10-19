 # SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# private driver headers for current Clock IP. This include PLL control and power headers
# this header being private, it is a part of the source set, instead of the include set
# Only the local directory sources can include it.
# this header is dynamically generated for the currently built platform. The driver
# source (C file) is selected automatically, but all driver sources include the
# very same header name, generated from corresponding svd
rcc_h = custom_target('gen_rcc',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('rcc'),
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'RCC', '@INPUT@' ],
)
sentry_source_set.add(rcc_h.to_list())

stm32_rcc_c_template = files('stm32-rcc.c.in')
stm32_rcc_c = dtsgen.process(stm32_rcc_c_template)

sentry_private_gen_source_set.add(stm32_rcc_c)

pwr_h = custom_target('gen_pwr',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('pwr'),
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'PWR', '@INPUT@' ],
)
sentry_source_set.add(pwr_h.to_list())

# driver source selection
sentry_source_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: files('stm32-pwr.c'))
