# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

flash_defs_h = custom_target('gen_flash',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('flash'),
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'FLASH', '@INPUT@' ],
)
sentry_source_set.add(flash_defs_h.to_list())

stm32f4_flash_c_template = files('stm32f4-flash.c.in')
stm32f4_flash_c = dtsgen.process(stm32f4_flash_c_template)
sentry_private_gen_source_set.add(when: 'CONFIG_SOC_SUBFAMILY_STM32F4', if_true: stm32f4_flash_c)
