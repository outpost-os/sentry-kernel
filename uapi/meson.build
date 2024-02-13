# UAPI header generation is always required

pkg_config = import('pkgconfig')
uapi_rust_std = 'rust_std=2021'
uapi_rust_libfile = files('src/lib.rs')
uapi_cbindgen_toml = files('cbindgen_uapi.toml')

cbindgen = find_program('cbindgen')

subdir('include/uapi')
subdir('src')

if with_uapi_opt

# XXX:
#  This deps is designed for userspace (libshied) only
#  As in linux kernel, uapi headers are not used w/ a kernel name and/or uapi
#  prefix. So, add the uapi include subdir in "include_directories".
sentry_c_uapi_dep = declare_dependency(
    link_with: uapi_rs_lib,
    sources: [ uapi_h ],
    dependencies: sentry_c_uapi_headers_dep,
    compile_args: [ global_build_args, target_arch_args ],
    include_directories: [ userspace_uapi_include_dir ],
)

pkg_config.generate(
    uapi_rs_lib,
    filebase: 'uapi',
    extra_cflags: [ global_build_args, target_arch_args ]
)

endif
