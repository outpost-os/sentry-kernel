# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

test_io = executable(
    'test_io',
    sources: files('test_io.cpp'),
    include_directories: kernel_inc,
    override_options: ['cpp_std=gnu++20'],
    cpp_args: [
        '-DTEST_MODE=1',
        '-Wno-pedantic',
    ],
    c_args: '-DTEST_MODE=1',
    dependencies: [gtest_main ],
    link_language: 'cpp',
    native: true,
)

test('io',
     test_io,
     env: nomalloc,
     suite: 'ut-utils')
