# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

rcc_h = custom_target('gen_rcc',
    input: peripheral_defs_in,
    output: '@BASENAME@',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'RCC', '@INPUT@' ],
)
sentry_source_set.add(rcc_h.to_list())


if kconfig_data.get('CONFIG_ARCH_MCU_STM32F439', 0) == 1
sentry_source_set.add(files(
    'stm32f4xx-rcc.c',
    'stm32f4xx-pwr.h',
))
endif
