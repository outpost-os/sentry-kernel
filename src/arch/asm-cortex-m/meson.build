# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

sentry_source_set.add(files(
  'nvic.c',
  'thread.c',
  'mpu.c',
  'systick.c',
))

sentry_startup += files(
  'startup.S',
)

if config_data.get('CONFIG_ARCH_MCU_STM32F4', 0) == 1
  subdir('stm32f4xx')
else
  error('target not supported!')
endif
