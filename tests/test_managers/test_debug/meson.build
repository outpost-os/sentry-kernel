# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

test_printk = executable(
    'test_printk',
    sources: files(
        'test_printk.cpp',
        join_paths(meson.project_source_root(), 'src/managers/debug/log.c'),
    ),
    include_directories: kernel_inc,
    cpp_args: [
        '-DTEST_MODE=1',
        '-DCONFIG_BUILD_TARGET_DEBUG=1',
    ],
    c_args: [
        '-DTEST_MODE=1',
        '-DCONFIG_BUILD_TARGET_DEBUG=1',
    ],
    dependencies: [gtest_main ],
    link_language: 'cpp',
    native: true,
)

test('printk',
     test_printk,
     env: nomalloc,
     suite: 'ut-utils')
