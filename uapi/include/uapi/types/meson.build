systypes_lib = static_library(
    'systypes',
    sources : 'types.rs',
    rust_args: global_rust_build_args,
    override_options: [ uapi_rust_std ],
    install: true,
)
systypes_dep = declare_dependency(link_whole : systypes_lib)
