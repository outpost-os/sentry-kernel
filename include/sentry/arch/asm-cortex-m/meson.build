# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# list of statically defined headers
sentry_header_set.add(files(
    'io.h',
    'membarriers.h',
    'mpu.h',
    'mpu_pmsa_v7.h',
    'nvic.h',
    'platform.h',
    'scb.h',
    'soc.h',
    'system.h',
    'systick.h',
    'thread.h',
))

# generated headers
irq_def_h = custom_target('gen_irq_defs',
   input: irq_defs_in,
    output: '@BASENAME@',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

layout_h = custom_target('gen_layout',
    input: layout_in,
    output: '@BASENAME@',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

vtor_h = custom_target('gen_vtor',
    input: vtor_table_in,
    output: '@BASENAME@',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '@INPUT@' ],
)
sentry_header_set.add(
    irq_def_h.to_list(),
    layout_h.to_list(),
    vtor_h.to_list(),
)
