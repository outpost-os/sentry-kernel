# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

if meson.is_subproject()
warning('!!! Are you sure you want to build the autotest task as a subproject ?')
endif

autotest_task_name = 'autotest'

# populated in src
autotest_ldscript_template = files()

subdir('src')

if get_option('with_tests') == false

autotest_ldscript = custom_target('autotest_ldscript',
    input: autotest_ldscript_template,
    output: '@BASENAME@',
    command: [ dts2src, '-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
)

autotest_linker_args = [
    '-T' + autotest_ldscript.full_path(),
    '-z', 'noexecstack',
]

autotest_map_file = '@0@.map'.format(autotest_task_name)

uapi_inc = include_directories('../uapi/include')

autotest_elf = executable(
    autotest_task_name,
    name_suffix: 'elf',
    sources: [autotest_sources ],
    include_directories: uapi_inc,
    dependencies: [ sentry_c_uapi_dep ],
    c_args: [ target_arch_args, global_build_args ],
    link_args: [ '-lgcc', target_arch_args, autotest_linker_args, '-Wl,-Map=@0@'.format(autotest_map_file)],
    link_language: 'c',
    link_depends: [ autotest_ldscript ],
    install: true,
)

autotest_hex = custom_target(
    input: autotest_elf,
    output: '@BASENAME@.hex',
    command: [
        objcopy,
        '-O', 'ihex',
        '@INPUT@',
        '@OUTPUT@'
    ],
    build_by_default: true,
    install: true,
    install_dir: get_option('bindir'),
    install_tag: 'runtime',
)

autotest_json = custom_target(
    input: autotest_elf,
    output: '@BASENAME@.json',
    command: [
        parseelf,
        '@INPUT@',
    ],
    build_by_default: true,
)

meson.add_install_script(sentry_install_script, autotest_map_file, get_option('infodir') / autotest_task_name)

endif
