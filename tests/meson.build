# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

hostcc = meson.get_compiler('c', native: true)
hostcc.has_function('__builtin_ffsl')

gtest_main = dependency('gtest_main', version: '>=1.13.0',
                         fallback : ['gtest', 'gtest_main_dep'],
                         native: true)

subdir('test_utils')
subdir('test_bsp')
