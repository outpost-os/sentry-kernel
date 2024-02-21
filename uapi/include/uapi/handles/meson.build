handles_lib = static_library(
    'handles',
    sources : 'handles.rs',
    rust_args: global_rust_build_args,
    override_options: [ uapi_rust_std ],
    install: false,
)
handles_dep = declare_dependency(link_with : handles_lib)
