project('sentry-kernel', 'c',
    meson_version: '>=1.1.0',
    version: run_command('dunamai', 'from', 'git', '--style', 'semver', '--dirty', check: true).stdout().strip(),
    default_options: ['c_std=gnu11', 'default_library=static', 'warning_level=3' ],
    license: 'Apache-2.0',
    license_files: [ 'LICENSE' ],
)

top_dir = meson.current_source_dir()

objcopy = find_program('objcopy')

# dunamai is used for version sync with gconf (in the same way poetry-dynamic-versioning does)
keyval = import('keyval')
fs = import('fs')
pymod = import('python')
ssmod = import('sourceset')

py3 = pymod.find_installation('python3', modules: ['dunamai'])

sentry_source_set = ssmod.source_set()

# kernel code shared include directory
kernel_inc = include_directories('include/sentry')

# userspace exported include directory
uapi_inc = include_directories('include/uapi')

# generated before calling meson
dotconfig = files('.config')


# Load configuration data from .config file
# keyval load convert .config to dict that can be use as input for configuration data
config_data = configuration_data(keyval.load(dotconfig))
# Fixup: convert .config entry set as `y` to boolean 10 (i.e. 1: true, 0: false)
# TODO: use true/false boolean instead
foreach k: config_data.keys()
    if config_data.get(k) == 'y'
        config_data.set10(k, true)
    endif
endforeach

# Generate configuration header from config_data
config_h = configure_file(
    configuration: config_data,
    output: 'config.h'
)

kernel_deps = []

global_build_args = [
    '-include', '@0@'.format(config_h),
    '-ffreestanding',
    '-fno-builtin',
    '-nostdlib',
    '-fno-common',
    '-Wno-unused-function', # FIXME: while in early dev
    '-Wno-unused-variable', # FIXME: while in early dev
    '-Wno-unused-parameter', # FIXME: while in early dev
]

target_arch_args = [
    config_data.get_unquoted('CONFIG_CPU_CFLAGS'),
    config_data.get_unquoted('CONFIG_ISA_CFLAGS'),
    config_data.get_unquoted('CONFIG_ENDIANNESS_CFLAGS'),
]

if config_data.get('CONFIG_FPU_SOFT_ABI', 0) != 1
target_arch_args += [
    config_data.get_unquoted('CONFIG_FPU_CFLAGS'),
    config_data.get_unquoted('CONFIG_FPU_ABI_CFLAGS'),
]
endif

add_project_link_arguments([
    target_arch_args,
    '-Wl,--gc-sections',
    '-Wl,--no-undefined',
    '-Wl,--cref',
    '-nostdlib',
    '-nodefaultlibs',
    '-nostartfiles'],
    language: 'c',
    native: false
)


add_global_arguments([ global_build_args, target_arch_args ], language: 'c', native: false)

# for ARM targets, using CMSIS headers
if config_data.get('CONFIG_ARCH_ARM', 0) == 1
cmsis_proj = subproject('cmsis')
cmsis_dep = cmsis_proj.get_variable('cmsis_dep')
kernel_deps += cmsis_dep
endif

# all sources are there
subdir('src')



message('build targetting SoC', config_data.get_unquoted('CONFIG_ARCH_SOCNAME'))


if config_data.get('CONFIG_BUILD_TARGET_RELEASE', 0) != 1
warning('!!! This is NOT a release build ! DO NOT USE IT IN PRODUCTION !!!')
endif

# auto-generation (jinja2, json) tooling is there
# subdir('tools')
