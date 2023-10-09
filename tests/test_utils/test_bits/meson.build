# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

test_bits = executable(
    'test_bits',
    sources: files('test_bits.cpp'),
    include_directories: kernel_inc,
    cpp_args: '-DTEST_MODE=1',
    c_args: '-DTEST_MODE=1',
    dependencies: [gtest_main ],
    link_language: 'cpp',
    native: true,
)

test('bits',
     test_bits,
     suite: 'ut-utils')
