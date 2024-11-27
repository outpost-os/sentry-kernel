# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

if not with_uapi_opt
    subdir_done()
endif

add_languages('rust', native: false, required: true)

# Set rust toolchain config entry according to kconfig
# Note:
#   configuration_file is done at top level meson.build in order to generate
#   rust-toolchain.toml at build root directory.
rust_toolchain_in = files('rust-toolchain.toml.in')
rust_toolchain_config = configuration_data()
rust_toolchain_config.set('channel', get_option('rust-channel'))
rust_toolchain_config.set('target', kconfig_data.get_unquoted('CONFIG_RUSTC_TARGET'))

rust_edition = '2021'
uapi_rust_std = 'rust_std=' + rust_edition

global_rust_build_args = [
    '@' + fs.parent(kconfig_rustargs) / fs.name(kconfig_rustargs),
    target_rustargs,
    '-C', 'lto=true', '-C', 'relocation-model=pic', '-C', 'link-args=--emit-relocs'
]

subdir('include/uapi')
subdir('uapi')

py3 = pymod.find_installation('python3', modules: ['git'])

# XXX:
#  This deps is designed for userspace (libshied) only
#  As in linux kernel, uapi headers are not used w/ a kernel name and/or uapi
#  prefix. So, add the uapi include subdir in "include_directories".
sentry_c_uapi_dep = declare_dependency(
    link_with: uapi_lib,
    sources: [ uapi_h ],
    compile_args: [ global_build_args, target_arch_args ],
    include_directories: [ userspace_uapi_include_dir ],
)

pkg_config = import('pkgconfig')
pkg_config.generate(
    uapi_lib,
    filebase: 'uapi',
    extra_cflags: [ global_build_args, target_arch_args ],
)

install_data(
  'task.Kconfig',
  install_dir : get_option('datadir') / 'configs',
)

summary(
    {
        'rust edition': rust_edition,
    },
    section: 'Target specific compile args'
)
