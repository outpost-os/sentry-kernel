# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

sentry_source_set.add(files(
  'nvic.c',
  'thread.c',
  'mpu.c',
  'systick.c',
))

sentry_startup += files(
  'handler.c',
)

sentry_vtor_template = files('vtor.c.in')

sentry_vtor_c = custom_target('gen_vtor',
  input: sentry_vtor_template,
  output: '@BASENAME@',
  depends: [ svd_json ],
  command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

sentry_startup += sentry_vtor_c

sentry_ldscript_template = files('cortex-m-sentry.ld.in')
