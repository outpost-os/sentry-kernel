paste_proj = subproject('paste-rs', version: '>= 1.0.14')
paste_dep = paste_proj.get_variable('paste_dep')

handles_lib = static_library(
    'handles',
    sources : 'handles.rs',
    dependencies : [paste_dep],
    rust_args: global_rust_build_args,
    override_options: [ uapi_rust_std ],
    install: true,
)
handles_dep = declare_dependency(link_whole : handles_lib, dependencies : [paste_dep])
