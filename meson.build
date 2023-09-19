project('sentry-kernel', 'c',
    meson_version: '>=1.1.0',
    version: run_command('dunamai', 'from', 'git', '--style', 'semver', '--dirty', check: true).stdout().strip(),
    default_options: ['c_std=gnu11', 'default_library=static', 'warning_level=2' ],
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
sentry_header_set = ssmod.source_set()

kconfig_file = meson.current_source_dir() / 'Kconfig'
kconfig_proj = subproject('kconfig', default_options: ['kconfig=@0@'.format(kconfig_file)])
kconfig_h = kconfig_proj.get_variable('kconfig_h')
kconfig_data = kconfig_proj.get_variable('kconfig_data')

sentry_header_set.add(kconfig_h)

# kernel code shared include directory. kernel include both kernel & user api
kernel_inc = include_directories('include')

# userspace exported include directory
uapi_inc = include_directories('include/uapi')

external_deps = []

global_build_args = [
    '-include', '@0@'.format(kconfig_h),
    '-ffreestanding',
    '-fno-builtin',
    '-nostdlib',
    '-fno-common',
    '-Wno-pedantic', # FIXME: to analyze bits.h (not pedantic compatible)
    '-Wno-unused-function', # FIXME: while in early dev
    '-Wno-unused-variable', # FIXME: while in early dev
    '-Wno-unused-parameter', # FIXME: while in early dev
]

# these flags are overload by arch/<architecture> meson.build file
target_arch_args = []

add_project_link_arguments([
    '-Wl,--gc-sections',
    '-Wl,--no-undefined',
    '-Wl,--cref',
    '-nostdlib',
    '-nodefaultlibs',
    '-nostartfiles'],
    language: 'c',
    native: false
)

# XXX: add_global_arguments **can't** be done after a subproject definition
#add_global_arguments([ global_build_args, target_arch_args ], language: 'c', native: false)
global_host_c_args_str = ','.join(global_build_args)

# for ARM targets, using CMSIS headers
if kconfig_data.get('CONFIG_ARCH_ARM', 0) == 1
cmsis_proj = subproject('cmsis', default_options: ['c_args=@0@'.format(global_host_c_args_str)])
cmsis_dep = cmsis_proj.get_variable('cmsis_dep')
external_deps += cmsis_dep
endif

# meson svd subproject and associated variables
meson_svd_proj = subproject('meson-svd',  default_options: 'svd=@0@'.format(kconfig_data.get_unquoted('CONFIG_ARCH_SOCNAME').to_lower()))

peripheral_defs_in = meson_svd_proj.get_variable('peripheral_defs_in')
svd_json = meson_svd_proj.get_variable('svd_json')
jinja_cli = meson_svd_proj.get_variable('jinja_cli')
layout_in = meson_svd_proj.get_variable('layout_in')

# sentry header set is populated in the include dir
subdir('include/sentry')
sentry_header_set_config = sentry_header_set.apply(kconfig_data, strict: false)

# all sources are there, sentry source set is populated in each subdir
subdir('src')

with_doc_opt = get_option('with_doc')
if with_doc_opt
  subdir('doc')
endif

meson.install_dependency_manifest('manifest.json')



# here we define the final target: the Sentry kernel binary
sentry_linker_args = [
    '-T@0@'.format(fs.name(sentry_linker_script[0])),
    '-L@0@'.format(sentry_linker_script_path),
]

sentry_map_file = '@0@.map'.format(meson.project_name())

sentry_elf = executable(
    meson.project_name(),
    name_suffix: 'elf',
    sources: [sentry_startup, sentry_header_set_config.sources() ],
    include_directories: kernel_inc,
    dependencies: [sentry_dep, external_deps],
    c_args: [ target_arch_args, global_build_args ],
    link_args: [ sentry_linker_args, '-Wl,-Map=@0@'.format(sentry_map_file)],
    link_language: 'c',
    link_depends: sentry_linker_script,
    install: true,
    install_dir: '',
)

sentry_map = custom_target(
    input: sentry_elf,
    output: sentry_map_file,
    command: ['touch', '@OUTPUT@'],
    build_by_default: true,
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


message('build targetting SoC', kconfig_data.get_unquoted('CONFIG_ARCH_SOCNAME'))

if kconfig_data.get('CONFIG_BUILD_TARGET_RELEASE', 0) != 1
warning('!!! This is NOT a release build ! DO NOT USE IT IN PRODUCTION !!!')
endif

# auto-generation (jinja2, json) tooling is there
# subdir('tools')
