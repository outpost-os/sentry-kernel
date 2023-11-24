# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

test_task = executable(
    'test_task',
    sources: files(
        'test_task.cpp',
        join_paths(meson.project_source_root(), 'kernel/src/managers/task/task_init.c'),
        join_paths(meson.project_source_root(), 'kernel/src/managers/task/task_idle.c'),
        join_paths(meson.project_source_root(), 'kernel/src/managers/task/task_core.c'),
    ),
    include_directories: kernel_inc,
    cpp_args: [
        '-DTEST_MODE=1',
        '-DCONFIG_BUILD_TARGET_DEBUG=1',
        '-include', '@0@'.format(kconfig_h),
    ],
    c_args: [
        '-DTEST_MODE=1',
        '-DCONFIG_BUILD_TARGET_DEBUG=1',
        '-include', '@0@'.format(kconfig_h),
    ],
    dependencies: [gtest_main ],
    link_language: 'cpp',
    native: true,
)

test('task',
     test_task,
     env: nomalloc,
     suite: 'ut-managers')
