# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

target_arch_args += [
    '-mcpu=cortex-@0@'.format(config_data.get_unquoted('CONFIG_ARCH_ARM_CORTEX_NAME')),
    config_data.get_unquoted('CONFIG_ISA_CFLAGS'),
    config_data.get_unquoted('CONFIG_ENDIANNESS_CFLAGS'),
]

if config_data.get('CONFIG_FPU_SOFT_ABI', 0) != 1
target_arch_args += [
    config_data.get_unquoted('CONFIG_FPU_ABI_CFLAGS'),
]
endif


sentry_source_set.add(files(
  'nvic.c',
  'thread.c',
  'mpu.c',
  'systick.c',
))

sentry_startup += files(
  'startup.S',
)

# include SoC-specific meson file, local path forged from the .config SoC name
subdir(config_data.get_unquoted('CONFIG_ARCH_SOCNAME').to_lower())
