bitflags_opts = [uapi_rust_std]
if meson.has_external_property('rust_target')
    bitflags_opts += ['target=@0@'.format(meson.get_external_property('rust_target'))]
endif

bitflags_proj = subproject('bitflags-rs', version: '>= 2.4.0', default_options: bitflags_opts)
bitflags_dep = bitflags_proj.get_variable('bitflags_dep')

capability_rs = files('capability.rs')
capability_toml = files('Cargo.toml')
capability_h_toml = files('capability.h.toml')

capabilities_lib = static_library(
    'capabilities',
    sources: capability_rs,
    dependencies: [bitflags_dep],
    rust_args: global_rust_build_args,
    override_options: [ uapi_rust_std ],
    install: false,
)

capability_cbindgen = {
    'toml': capability_h_toml,
    'depend_files': [capability_rs, capability_toml],
    'depends': capabilities_lib,
}
uapi_cbindgen_configs += [capability_cbindgen]

capabilities_dep = declare_dependency(link_with : capabilities_lib, dependencies : [bitflags_dep])
