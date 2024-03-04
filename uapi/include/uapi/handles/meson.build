
handles_rs = files('handles.rs')
handles_toml = files('Cargo.toml')
handles_h_toml = files('handle.h.toml')

handles_lib = static_library(
    'handles',
    sources : handles_rs,
    rust_args: global_rust_build_args,
    override_options: [ uapi_rust_std ],
    install: false,
)
handles_dep = declare_dependency(link_with : handles_lib)

handles_cbindgen = {
    'toml': handles_h_toml,
    'depend_files': [handles_rs, handles_toml],
    'depends': handles_lib,
}
uapi_cbindgen_configs += [handles_cbindgen]
