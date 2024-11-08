# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0


# note: to avoid printf implementation redundancy, the kernel lexer for debug
# print mode is used as-is
autotest_sources = files(
  'main.c',
  'printf.c',
  'ssp.c',
  'tests/test_ipc.c',
  'tests/test_signal.c',
  'tests/test_handle.c',
  'tests/test_sleep.c',
  'tests/test_cycles.c',
  'tests/test_yield.c',
  'tests/test_random.c',
  'tests/test_gpio.c',
  'tests/test_map.c',
  'tests/test_shm.c',
  'tests/test_dma.c',
  'tests/test_irq.c',
  '../../kernel/src/managers/debug/log_lexer.c',
)

subdir('arch')
subdir('drivers')
