# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

if meson.is_subproject()
warning('!!! Are you sure you want to build the Idle task as a subproject ?')
endif

idle_task_name = 'idle'

# populated in src
sentry_ldscript_template = files()

subdir('src')

if get_option('with_tests') == false

idle_ldscript = custom_target('idle_ldscript',
    input: idle_ldscript_template,
    output: '@BASENAME@',
    command: [ dts2src, '-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
)

idle_linker_args = [
    '-T' + idle_ldscript.full_path(),
    '-z', 'noexecstack',
]

idle_map_file = '@0@.map'.format(idle_task_name)

uapi_inc = include_directories('../uapi/include')

idle_elf = executable(
    idle_task_name,
    name_suffix: 'elf',
    sources: [idle_sources ],
    include_directories: uapi_inc,
    dependencies: [ sentry_c_uapi_dep ],
    c_args: [ target_arch_args, global_build_args ],
    link_args: [ '-lgcc', target_arch_args, idle_linker_args, '-Wl,-Map=@0@'.format(idle_map_file)],
    link_language: 'c',
    link_depends: [ idle_ldscript ],
    install: true,
)

idle_hex = custom_target(
    input: idle_elf,
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

meson.add_install_script(sentry_install_script, idle_map_file, get_option('infodir') / idle_task_name)

endif
