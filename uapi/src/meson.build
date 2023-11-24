rust = import('rust')

bitflags_dep = dependency('bitflags-rs', version : '>=2.4.0')
uapi_rs_lib = static_library(
    'uapi',
    sources : 'lib.rs',
    rust_abi: 'c',
    dependencies : [bitflags_dep, systypes_dep],
    rust_args: global_rust_build_args,
)

libuapirs_dep = declare_dependency(link_with : uapi_rs_lib)
