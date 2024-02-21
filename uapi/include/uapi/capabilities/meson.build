bitflags_opts = [uapi_rust_std]
if meson.has_external_property('rust_target')
    bitflags_opts += ['target=@0@'.format(meson.get_external_property('rust_target'))]
endif

bitflags_proj = subproject('bitflags-rs', version: '>= 2.4.0', default_options: bitflags_opts)
bitflags_dep = bitflags_proj.get_variable('bitflags_dep')

capabilities_lib = static_library(
    'capabilities',
    sources : 'capability.rs',
    dependencies : [bitflags_dep],
    rust_args: global_rust_build_args,
    override_options: [ uapi_rust_std ],
    install: false,
)
capabilities_dep = declare_dependency(link_with : capabilities_lib, dependencies : [bitflags_dep])
