# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

if kconfig_data.get('CONFIG_ARCH_ARM_CORTEX_M', 0) == 1
subdir('asm-cortex-m')
endif

# architecture-generic, but architecture related code
sentry_source_set.add(files(
  'asm-generic/platform.c',
  'asm-generic/sync.c',
  'asm-generic/panic.c',
))
