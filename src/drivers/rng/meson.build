# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# private driver header for current GPIO IPs
# this header being private, it is a part of the source set, instead of the include set
# Only the local directory sources can include it.
# this header is dynamically generated for the currently built platform. The driver
# source (C file) is selected automatically, but all driver sources include the
# very same header name, generated from corresponding svd
rng_h = custom_target('gen_rng',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('rng'),
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'RNG', '@INPUT@' ],
)
sentry_source_set.add(rng_h.to_list())

# driver source selection
if kconfig_data.get('CONFIG_ARCH_MCU_STM32F439', 0) == 1
sentry_source_set.add(files(
    'stm32f4xx-rng.c'
))
endif
