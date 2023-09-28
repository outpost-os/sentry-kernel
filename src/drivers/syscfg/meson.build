# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# private driver header for current Syscfg IPs
# this header being private, it is a part of the source set, instead of the include set
# Only the local directory sources can include it.
# this header is dynamically generated for the currently built platform. The driver
# source (C file) is selected automatically, but all driver sources include the
# very same header name, generated from corresponding svd
syscfg_h = custom_target('gen_syscfg',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('syscfg'),
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'SYSCFG', '@INPUT@' ],
)
sentry_source_set.add(syscfg_h.to_list())

# driver source selection
if kconfig_data.get('CONFIG_SOC_SUBFAMILY_STM32F4', 0) == 1
sentry_source_set.add(files(
    'stm32f4-syscfg.c'
))
endif
