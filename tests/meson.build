# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

hostcc = meson.get_compiler('c', native: true)
hostcc.has_function('__builtin_ffsl')

gtest_main = dependency('gtest_main', version: '>=1.13.0',
                         fallback : ['gtest', 'gtest_main_dep'],
                         native: true)

test_args = []
# Extra flags if coverage is enabled
if get_option('b_coverage')
test_args += [
    '-fprofile-abs-path',
    '-fsanitize=undefined',
    '-fsanitize-address-use-after-scope',
    '-fstack-protector-strong',
    '-fno-inline',
    '-fno-inline-small-functions',
    '-fno-default-inline',
    '-DTEST_MODE=1',
]

add_project_link_arguments(
[
    '-fsanitize=undefined',
    '-fsanitize-address-use-after-scope',
    '-fstack-protector-strong',
],
language: ['c', 'cpp'],
)
endif

subdir('test_utils')
