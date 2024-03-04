
types_rs = files('types.rs')
types_toml = files('Cargo.toml')
types_h_toml = files('types.h.toml')

systypes_lib = static_library(
    'systypes',
    sources : types_rs,
    rust_args: global_rust_build_args,
    override_options: [ uapi_rust_std ],
    install: false,
)
systypes_dep = declare_dependency(link_with : systypes_lib)

types_cbindgen = {
    'toml': types_h_toml,
    'depend_files': [types_rs, types_toml],
    'depends': systypes_lib,
}
uapi_cbindgen_configs += [types_cbindgen]
