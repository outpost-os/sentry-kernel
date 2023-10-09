# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

test_io = executable(
    'test_io',
    sources: files('test_io.cpp'),
    include_directories: kernel_inc,
    cpp_args: test_args, 
    c_args: test_args, 
    dependencies: [gtest_main ],
    link_language: 'cpp',
    native: true,
)

test('io',
     test_io,
     suite: 'ut-utils')
