# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

test_printk = executable(
    'test_printk',
    sources: [
        files(
            'test_printk.cpp',
            join_paths(meson.project_source_root(), 'kernel/src/managers/debug/log.c'),
            join_paths(meson.project_source_root(), 'kernel/src/managers/debug/log_lexer.c'),
        ),
        sentry_header_set_config.sources(),
    ],
    include_directories: kernel_inc,
    override_options: ['cpp_std=gnu++20'],
    cpp_args: [
        '-DTEST_MODE=1',
        '-DCONFIG_BUILD_TARGET_DEBUG=1',
    ],
    c_args: [
        '-DTEST_MODE=1',
        '-DCONFIG_BUILD_TARGET_DEBUG=1',
        '-include', join_paths(fs.parent(kconfig_h),fs.name(kconfig_h)),
    ],
    dependencies: [gtest_main],
    link_language: 'cpp',
    native: true,
)

test('printk',
     test_printk,
     env: nomalloc,
     suite: 'ut-managers')
