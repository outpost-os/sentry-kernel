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
