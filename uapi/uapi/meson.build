rust = import('rust')

if not with_uapi_opt
    subdir_done()
endif

uapi_rs_lib = static_library(
    'uapi',
    sources : uapi_rust_libfile,
    rust_abi: 'c',
    rust_args: global_rust_build_args,
    override_options: [uapi_rust_std],
    install: true,
)

libuapirs_dep = declare_dependency(link_with : uapi_rs_lib)
