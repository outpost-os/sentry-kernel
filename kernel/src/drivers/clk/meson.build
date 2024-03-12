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

if kconfig_data.get('CONFIG_SOC_FAMILY_STM32', 0) == 1
stm32_rcc_c_template = files('stm32-rcc.c.in')
stm32_rcc_h_template = files('stm32-rcc.h.in')

stm32_rcc_dt_c_template = files('stm32-rcc-dt.c.in')
stm32_rcc_dt_h_template = files('stm32-rcc-dt.h.in')

stm32_rcc_c = dtsgen.process(stm32_rcc_c_template)
stm32_rcc_h = dtsgen.process(stm32_rcc_h_template)

stm32_rcc_dt_c = dtsgen.process(stm32_rcc_dt_c_template)
stm32_rcc_dt_h = dtsgen.process(stm32_rcc_dt_h_template)

sentry_private_gen_source_set.add(stm32_rcc_c, stm32_rcc_dt_c)
sentry_private_gen_header_set.add(stm32_rcc_h, stm32_rcc_dt_h)
endif

# XXX: there is no OR clause in source set
sentry_source_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32F4', if_true: files('stm32x4-pll.c'))
sentry_source_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32L4', if_true: files('stm32x4-pll.c'))

sentry_source_set.add(
    when: 'CONFIG_SOC_SUBFAMILY_STM32U5',
    if_true: files(
        'stm32u5-pll.c',
        'stm32u5-pwr.c',
        'stm32u5-pwr.h',
    ),
)

# per subfamily RCC additions
if kconfig_data.get('CONFIG_SOC_SUBFAMILY_STM32F4', 0) == 1
stm32f4_rcc_c_template = files('stm32f4-rcc.c.in')
stm32f4_rcc_h_template = files('stm32f4-rcc.h.in')

stm32f4_rcc_c = dtsgen.process(stm32f4_rcc_c_template)
stm32f4_rcc_h = dtsgen.process(stm32f4_rcc_h_template)

sentry_private_gen_source_set.add(stm32f4_rcc_c)
sentry_private_gen_header_set.add(stm32f4_rcc_h)
endif

if kconfig_data.get('CONFIG_SOC_SUBFAMILY_STM32L4', 0) == 1
stm32l4_rcc_c_template = files('stm32l4-rcc.c.in')
stm32l4_rcc_h_template = files('stm32l4-rcc.h.in')

stm32l4_rcc_c = dtsgen.process(stm32l4_rcc_c_template)
stm32l4_rcc_h = dtsgen.process(stm32l4_rcc_h_template)

sentry_private_gen_source_set.add(stm32l4_rcc_c)
sentry_private_gen_header_set.add(stm32l4_rcc_h)
endif

if kconfig_data.get('CONFIG_SOC_SUBFAMILY_STM32U5', 0) == 1
stm32u5_rcc_c_template = files('stm32u5-rcc.c.in')
stm32u5_rcc_h_template = files('stm32u5-rcc.h.in')

stm32u5_rcc_c = dtsgen.process(stm32u5_rcc_c_template)
stm32u5_rcc_h = dtsgen.process(stm32u5_rcc_h_template)

sentry_private_gen_source_set.add(stm32u5_rcc_c)
sentry_private_gen_header_set.add(stm32u5_rcc_h)
endif

pwr_h = custom_target('gen_pwr',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('pwr'),
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'PWR', '@INPUT@' ],
)
sentry_source_set.add(pwr_h.to_list())

# driver source selection
sentry_source_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: files('stm32-pwr.c'))
