# UAPI header generation is always required

uapi_rust_std = 'rust_std=2021'
uapi_rust_libfile = files('src/lib.rs')

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
    dependencies: [ libuapirs_dep ],
    compile_args: [ global_build_args, target_arch_args ],
    include_directories: [ userspace_uapi_include_dir ],
)

endif
