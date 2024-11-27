# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

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

# Generate pkg config file uapi.pc for C app using c_ffi static library
pkg_config = import('pkgconfig')
pkg_config.generate(
    uapi_lib,
    filebase: 'uapi',
    extra_cflags: [ global_build_args, target_arch_args ],
)



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
