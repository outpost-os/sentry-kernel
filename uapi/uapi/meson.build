# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

rust = import('rust')

uapi_rs_lib = static_library(
    'uapi',
    sources : uapi_rust_libfile,
    rust_abi: 'c',
    rust_args: global_rust_build_args,
    override_options: [uapi_rust_std],
    install: true,
)

libuapirs_dep = declare_dependency(link_with : uapi_rs_lib)

cargo = find_program('cargo', required: true)

if with_doc_opt
gen_cargo_doc = custom_target(
  'forge_cargo_doc',
  output: 'doc',
  command: [
    cargo,
    'doc',
    '--lib',
    '--package', 'sentry-uapi',
    '--examples',
    '--manifest-path', meson.current_source_dir() / 'Cargo.toml'
  ],
  install: true,
  env: {'CARGO_TARGET_DIR':meson.current_build_dir()},
  install_dir: get_option('datadir') / 'doc/sentry-uapi',
  install_tag: 'doc',
  build_by_default: true,
  build_always_stale: true,
)
endif # with_doc

if with_tests
cargo_options = [ '--manifest-path', meson.current_source_dir() / 'Cargo.toml' ]
cargo_options += [ '--target-dir', meson.current_build_dir() ]

cargo_env = environment()
# it seems that flatpak can't access network during install stage.
#cargo_env.set('CARGO_HOME', meson.project_build_root() / 'cargo-home')
#cargo_env.set('CODEGEN_BUILD_DIR', meson.current_build_dir())

test(
  'rust-fmt',
  cargo,
  args: [
    'fmt',
    cargo_options,
    '--',
    '--check',
  ],
  depends: uapi_rs_lib,
  env: cargo_env,
  is_parallel: false,
  timeout: 1800,
  should_fail: true,
  suite: 'uapi',
)

cargo_clippy = find_program('cargo-clippy', required: false)
if cargo_clippy.found()
  test(
    'rust-clippy',
    cargo_clippy,
    args: [
      cargo_options,
      '--no-deps',
      '--',
      '-D',
      'warnings',
    ],
    depends: uapi_rs_lib,
    env: cargo_env,
    should_fail: true,
    suite: 'uapi',
  )
endif

test(
  'rust-test',
  cargo,
  args: [
    'test',
    cargo_options,
    '--',
    '--test-threads=1',
  ],
  depends: uapi_rs_lib,
  env: cargo_env,
  is_parallel: false,
  timeout: 1800,
  should_fail: true,
  suite: 'uapi',
)

endif #with_tests
