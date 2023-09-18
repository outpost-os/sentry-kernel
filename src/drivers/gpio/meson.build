# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

gpio_h = custom_target('gen_gpio',
    input: peripheral_defs_in,
    output: '@BASENAME@',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'GPIO', '@INPUT@' ],
)
sentry_source_set.add(gpio_h.to_list())
