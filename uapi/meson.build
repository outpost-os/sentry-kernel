# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

if not with_uapi_opt
    subdir_done()
endif

if not meson.has_external_property('rust_target')
    error('missing rust_target property in cross-file')
endif

add_languages('rust', native: false, required: true)

rust_toolchain_in = files('rust-toolchain.toml.in')
rust_toolchain_config = configuration_data()
rust_toolchain_config.set('channel', get_option('rust-channel'))
rust_toolchain_config.set('target', kconfig_data.get_unquoted('CONFIG_RUSTC_TARGET'))

uapi_rust_std = 'rust_std=2021'
uapi_rust_libfile = files('uapi/lib.rs')

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
    link_with: uapi_rs_lib,
    sources: [ uapi_h ],
    compile_args: [ global_build_args, target_arch_args ],
    include_directories: [ userspace_uapi_include_dir ],
)

pkg_config = import('pkgconfig')
pkg_config.generate(
    uapi_rs_lib,
    filebase: 'uapi',
    extra_cflags: [ global_build_args, target_arch_args ],
)

install_data(
  'task.Kconfig',
  install_dir : get_option('datadir') / 'configs',
)

install_subdir(
  'uapi',
  install_dir: get_option('datadir') / 'cargo/repository/sentry-uapi',
  strip_directory: true,
  install_tag: 'devel',
)

vendoring_py_wrapper = '''
import git

repo = git.Repo(search_parent_directories=True)
print('{');
print('  "git": {')
print('    "sha1": "{}"'.format(repo.head.commit.tree.hexsha))
print('}');
'''

gen_cargo_hash = custom_target(
  'forge_cargo_hashfile',
  output: '.cargo_vcs_info.json',
  command: [ py3, '-c', vendoring_py_wrapper ],
  capture: true,
  install: true,
  install_dir: get_option('datadir') / 'cargo/repository/sentry-uapi',
  install_tag: 'devel',
  build_by_default: true,
)

install_data(
  'task.Kconfig',
  install_dir : get_option('datadir') / 'configs',
)

install_data(
  '.cargo-checksum.json',
  install_dir: get_option('datadir') / 'cargo/repository/sentry-uapi',
)
