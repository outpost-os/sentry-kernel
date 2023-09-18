# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

peripheral_defs_in = meson_svd_proj.get_variable('peripheral_defs_in')

jinja_gen = generator(jinja_cli,
       output: '@BASENAME@',
       arguments: ['-d', '@0@'.format(svd_json),
                   '-o', '@OUTPUT@',
                   '@EXTRA_ARGS@',
                   '@INPUT@'],
       depends: [ svd_json ])

subdir('gpio')
subdir('clk')
