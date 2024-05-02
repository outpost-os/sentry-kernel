# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

test_bits = executable(
    'test_bits',
    sources: [ files('test_bits.cpp'), sentry_header_set_config.sources() ],
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

test('bits',
     test_bits,
     env: nomalloc,
     suite: 'ut-utils')
