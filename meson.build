project('sentry-kernel',
    ['c','cpp','rust'],
    meson_version: '>=1.3.0',
    default_options: [
        'c_std=gnu11', 'cpp_std=gnu++20', 'rust_std=2021',
        'warning_level=3', 'optimization=s',
        'default_library=static', 'b_pie=false', 'b_staticpic=false'
    ],
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

if meson.has_external_property('rust_target')
    add_global_arguments([
        '--target=@0@'.format(meson.get_external_property('rust_target'))
    ], language: 'rust', native: false)
else
    warning('No `rust_target` defined, build will fail unless it is only docs.')
endif

kconfig_file = meson.current_source_dir() / 'Kconfig'
kconfig_proj = subproject('kconfig', default_options: ['kconfig=@0@'.format(kconfig_file)])
kconfig_h = kconfig_proj.get_variable('kconfig_h')
kconfig_data = kconfig_proj.get_variable('kconfig_data')

# userspace exported include directory, also used by kernel
uapi_inc = include_directories('uapi/include')

external_deps = []

global_build_args = [
    '-include', '@0@'.format(kconfig_h),
    '-ffreestanding',
    '-fno-builtin',
    '-nostdlib',
    '-fno-common',
    '-fdata-sections',
    '-ffunction-sections',
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

# XXX: we may found another to do so, default options are sets once and for all
# as this input comes from config file, **and**, any changes in dotconfig fires
# a project reconfiguration without changing default options. This breaks the
# rule of least suprise.
# TODO: use a common option in all (sub)project w/ yield property to use the same
# configuration data in all components.
devicetree_proj = subproject('devicetree', default_options: 'dts=@0@/@1@'.format(
    meson.current_source_dir(), kconfig_data.get_unquoted('CONFIG_DTS_FILE').to_lower()))
dts = devicetree_proj.get_variable('devicetree_dtsd')
dts2src = devicetree_proj.get_variable('dts2src')
devicetree_dep = devicetree_proj.get_variable('devicetree_dep')
external_deps += devicetree_dep

dtsgen = generator(dts2src,
    arguments: ['-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
    output: '@BASENAME@',
)

# all sources are there, sentry source set is populated in each subdir

with_uapi_opt = get_option('with_uapi')
with_kernel_opt = get_option('with_kernel')
with_idle_opt = get_option('with_idle')

# we first load sysgate build dep for uapi
subdir('uapi')

if with_kernel_opt or with_idle_opt
subdir('kernel')
endif



with_doc_opt = get_option('with_doc')
if with_doc_opt
  subdir('doc')
endif

with_proof_opt = get_option('with_proof')
if with_proof_opt
  subdir('proof')
endif

with_tests_opt = get_option('with_tests')
if with_tests_opt
    subdir('tests')
endif

meson.install_dependency_manifest('manifest.json')

message('build targetting SoC', kconfig_data.get_unquoted('CONFIG_ARCH_SOCNAME'))

if kconfig_data.get('CONFIG_BUILD_TARGET_RELEASE', 0) != 1
warning('!!! This is NOT a release build ! DO NOT USE IT IN PRODUCTION !!!')
endif

summary(
    {
        'soc': kconfig_data.get_unquoted('CONFIG_ARCH_SOCNAME').to_lower(),
        'dts': kconfig_data.get_unquoted('CONFIG_DTS_FILE').to_lower(),
    },
    section: 'Configuration'
)

# auto-generation (jinja2, json) tooling is there
# subdir('tools')
