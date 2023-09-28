# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

jinja_gen = generator(jinja_cli,
       output: '@BASENAME@',
       arguments: ['-d', '@0@'.format(svd_json),
                   '-o', '@OUTPUT@',
                   '@EXTRA_ARGS@',
                   '@INPUT@'],
       depends: [ svd_json ])

subdir('gpio')
subdir('clk')
subdir('rng')
subdir('exti')
subdir('syscfg')
