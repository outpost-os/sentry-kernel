project('sentry-kernel',
    ['c','cpp','rust'],
    meson_version: '>=1.3.0',
    default_options: [
        'c_std=gnu11', 'cpp_std=gnu++20', 'rust_std=2021',
        'warning_level=3', 'optimization=s',
        'default_library=static', 'b_pie=false', 'b_staticpic=false',
        'licensedir=share/info/sentry-kernel',
        'pkgconfig.relocatable=true',
    ],
    license: 'Apache-2.0',
    license_files: [ 'LICENSE' ],
)

top_dir = meson.current_source_dir()

objcopy = find_program('objcopy')
sentry_install_script = find_program('support/scripts/install.py')

# dunamai is used for version sync with gconf (in the same way poetry-dynamic-versioning does)
keyval = import('keyval')
fs = import('fs')
pymod = import('python')
ssmod = import('sourceset')

py3 = pymod.find_installation('python3', modules: ['dunamai'])

if meson.has_external_property('rust_target')
    add_project_arguments([
        '--target=@0@'.format(meson.get_external_property('rust_target')),
        '-C', 'lto=true', '-C', 'relocation-model=pic', '-C', 'link-args=--emit-relocs'
    ], language: 'rust', native: false)
else
    warning('No `rust_target` defined, build will fail unless it is only docs.')
endif

kconfig_file = meson.current_source_dir() / 'Kconfig'
kconfig_proj = subproject('kconfig', default_options: ['kconfig=@0@'.format(kconfig_file)])
kconfig_h = kconfig_proj.get_variable('kconfig_h')
kconfig_rustargs = kconfig_proj.get_variable('kconfig_rustargs')
kconfig_data = kconfig_proj.get_variable('kconfig_data')

external_deps = []

global_build_args = [
    '-include', fs.parent(kconfig_h) / fs.name(kconfig_h),
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

global_rust_build_args = [
   '@' + fs.parent(kconfig_rustargs) / fs.name(kconfig_rustargs)
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
# XXX: Using a default option here may lead to weird results if one changes the kconfig
# may be use a generator and process in the top level project ?!?
meson_svd_proj = subproject('meson-svd',  default_options: 'svd=@0@'.format(kconfig_data.get_unquoted('CONFIG_ARCH_SOCNAME').to_lower()))

peripheral_defs_in = meson_svd_proj.get_variable('peripheral_defs_in')
svd_json = meson_svd_proj.get_variable('svd_json')
jinja_cli = meson_svd_proj.get_variable('jinja_cli')
layout_in = meson_svd_proj.get_variable('layout_in')

devicetree_proj = subproject('devicetree')
dts = devicetree_proj.get_variable('devicetree_dtsd')
dts2src = devicetree_proj.get_variable('dts2src')
devicetree_dep = devicetree_proj.get_variable('devicetree_dep')
external_deps += devicetree_dep

# XXX: move to meson-devicetree ?
dtsgen = generator(dts2src,
    arguments: ['-d', dts.full_path() , '-t', '@INPUT@', '@OUTPUT@' ],
    depends: [ dts ],
    output: '@BASENAME@',
)

# all sources are there, sentry source set is populated in each subdir

with_uapi_opt = get_option('with_uapi')
with_kernel_opt = get_option('with_kernel')
with_idle_opt = get_option('with_idle')

subdir('tools')
subdir('support/arch')

# Idle implies libuapi
if with_idle_opt or kconfig_data.get('CONFIG_BUILD_TARGET_AUTOTEST', 0) == 1
    with_uapi_opt = true
endif

# at least uapi headers are generated libuapi build is under
# with_uapi option flag
subdir('uapi')

# building kernel
if with_idle_opt
subdir('idle')
endif

# building kernel
if kconfig_data.get('CONFIG_BUILD_TARGET_AUTOTEST', 0) == 1
subdir('autotest')
endif

# building idle
if with_kernel_opt
subdir('kernel')
endif

# schemas and tooling
subdir('schemas')

with_doc_opt = get_option('with_doc')
if with_doc_opt
  subdir('doc')
endif

message('build targetting SoC', kconfig_data.get_unquoted('CONFIG_ARCH_SOCNAME'))

if kconfig_data.get('CONFIG_BUILD_TARGET_AUTOTEST', 0) == 1
message('> This is an autotest standalone image')
endif
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

if kconfig_data.get('CONFIG_BUILD_TARGET_AUTOTEST', 0) == 1 and not get_option('with_tests')
# in autotest mode only, fusion all hex into one single hex, to simplify
# gdb flashing. This mode needs srec_cat to fusion all hex into one
# other nominal (debug, release) modes use build system based binary
# generation instead.
srec_cat = find_program('srec_cat', required: false, disabler: true)

if srec_cat.found()
firmware_hex = custom_target(
    depends: [ autotest_hex, idle_hex, sentry_hex ],
    output: 'firmware.hex',
    command: [
        srec_cat,
        '-o', '@OUTPUT@', '-Intel',
        sentry_hex.full_path(), '-Intel',
        idle_hex.full_path(), '-Intel',
        autotest_hex.full_path(), '-Intel',
    ],
    build_by_default: true,
)
else
warning('srec_cat utility not found!')
warning('!!! Unable to forge final hex automatically! help yourself with ELF and HEX...')
endif

endif

# auto-generation (jinja2, json) tooling is there
# subdir('tools')
