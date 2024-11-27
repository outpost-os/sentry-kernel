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

global_rust_build_args = [
    '@' + fs.parent(kconfig_rustargs) / fs.name(kconfig_rustargs),
    target_rustargs,
    '-C', 'lto=true', '-C', 'relocation-model=pic', '-C', 'link-args=--emit-relocs'
]

rust_edition = '2021'
uapi_rust_std = 'rust_std=' + rust_edition
uapi_manifest = files('Cargo.toml')

subdir('include/uapi')
subdir('src')

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
