sentry_source_set = ssmod.source_set()
sentry_header_set = ssmod.source_set()

sentry_header_set.add(kconfig_h)

# kernel code include both its own headers and UAPI headers
kernel_inc = include_directories(
    'include',
    '../uapi/include'
)


# populated in src
sentry_ldscript_template = files()

# sentry header set is populated in the include dir
# BSP is driver related headers. Drivers exported header are only used by
# managers. As such, there should not have <bsp/xx> path out of the managers
# source directory.
subdir('include/bsp')
# kernel-wide exported headers
subdir('include/sentry')
sentry_header_set_config = sentry_header_set.apply(kconfig_data, strict: false)

subdir('src')

# there is no mean in building a target ELF file with coverage functions added.
# It will not fit in target, and it will not be usable as is.
if get_option('with_tests') == false and with_kernel_opt
# XXX:
# For ldscript gen we use a custom target instead of the previously defined
# generator as we need to know the outputed filename at link time
# (FYI generator generates anonymous file that can be built bu we can't use
# the generated filename in any other target)
sentry_ldscript = custom_target('sentry_ldscript',
    input: sentry_ldscript_template,
    output: '@BASENAME@',
    command: [ dts2src, '-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
)

sentry_linker_args = [
    '-T@0@'.format(sentry_ldscript.full_path()),
    '-z', 'noexecstack',
]

sentry_map_file = '@0@.map'.format(meson.project_name())


sentry_elf = executable(
    meson.project_name(),
    name_suffix: 'elf',
    sources: [sentry_startup, sentry_header_set_config.sources() ],
    include_directories: kernel_inc,
    dependencies: [sentry_dep, external_deps, sentry_c_uapi_headers_dep ],
    c_args: [ target_arch_args, global_build_args ],
    link_args: [ '-lgcc', target_arch_args, sentry_linker_args, '-Wl,-Map=@0@'.format(sentry_map_file)],
    link_language: 'c',
    link_depends: [ sentry_ldscript ],
    install: true,
    install_dir: '',
)

sentry_bin = custom_target(
    input: sentry_elf,
    output: '@BASENAME@.bin',
    command: [objcopy, '--output-target=binary', '@INPUT@', '@OUTPUT@'],
    build_by_default: true,
    install: true,
    install_dir: '',
)

# TODO: Use an install hook instead of dummy target
needs_wsl = []
if build_machine.system() == 'windows'
    needs_wsl = ['wsl']
endif
sentry_map = custom_target(
    input: sentry_elf,
    output: sentry_map_file,
    command: needs_wsl + ['touch', '@OUTPUT@'],
    build_by_default: true,
    install: true,
    install_dir: '',
)
endif
