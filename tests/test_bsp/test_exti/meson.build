# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

test_bsp_exti = executable(
    'test_bsp_exti',
    sources: [
        files(
            'test_exti.cpp',
            join_paths(meson.project_source_root(), 'src/drivers/exti/stm32-exti.c')
        ),
        exti_h, stm32_exti_dtsgen_h,
    ],
    include_directories: kernel_inc,
    cpp_args: [
        '-I'+join_paths(meson.project_build_root(), 'src/drivers/exti'),
        '-include', '@0@'.format(kconfig_h),
        '-DTEST_MODE=1',
    ],
    c_args: [
        '-I'+join_paths(meson.project_build_root(), 'src/drivers/exti'),
        global_build_args,
        '-DTEST_MODE=1',
    ],
    dependencies: [ gtest_main, cmsis_dep ],
    link_language: 'cpp',
    native: true,
)

test('exti',
     test_bsp_exti,
     env: nomalloc,
     suite: 'ut-bsp')
