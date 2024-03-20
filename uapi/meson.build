# UAPI header generation is always required

pkg_config = import('pkgconfig')
uapi_rust_std = 'rust_std=2021'
uapi_rust_libfile = files('uapi/lib.rs')

subdir('systypes')
subdir('include/uapi')
subdir('uapi')

if with_uapi_opt

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

pkg_config.generate(
    uapi_rs_lib,
    filebase: 'uapi',
    extra_cflags: [ global_build_args, target_arch_args ],
)

install_data(
  'task.Kconfig',
  install_dir : get_option('datadir') / 'configs',
)

with_tests_opt = get_option('with_tests')
if with_tests_opt

cargo = find_program('cargo', required: true)

cargo_options = [ '--manifest-path', meson.project_source_root() / 'Cargo.toml' ]
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

endif #with_uapi
