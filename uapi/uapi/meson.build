# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

rust = import('rust')

uapi_manifest = files('Cargo.toml')
uapi_libfile = files('lib.rs')

# XXX:
# only lib.rs is required for static_library target but in order to export correct
# dependencies through meson introspect, we should add deps to inner modules
uapi_modules = files([
  'panic.rs',
  'svc_exchange.rs',
  'syscall.rs',
  'systypes.rs',
  'uapi.rs',
])

subdir('arch')

uapi_lib = static_library(
    'uapi',
    sources : uapi_libfile,
    rust_abi: 'c',
    rust_args: global_rust_build_args,
    override_options: [uapi_rust_std],
    extra_files: uapi_modules,
    install: true,
)

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
    '--manifest-path', uapi_manifest[0].full_path(),
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
cargo_options = [ '--manifest-path', uapi_manifest[0].full_path() ]
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
  depends: uapi_lib,
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
    depends: uapi_lib,
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
  depends: uapi_lib,
  env: cargo_env,
  is_parallel: false,
  timeout: 1800,
  should_fail: true,
  suite: 'uapi',
)

endif #with_tests
