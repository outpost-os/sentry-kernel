rust = import('rust')

if not with_uapi_opt
    subdir_done()
endif

bitflags_opts = [uapi_rust_std]
if meson.has_external_property('rust_target')
    bitflags_opts += ['target=@0@'.format(meson.get_external_property('rust_target'))]
endif

bitflags_proj = subproject('bitflags-rs', version: '>= 2.4.0', default_options: bitflags_opts)
bitflags_dep = bitflags_proj.get_variable('bitflags_dep')

uapi_rs_lib = static_library(
    'uapi',
    sources : uapi_rust_libfile,
    rust_abi: 'c',
    dependencies : [bitflags_dep, systypes_dep],
    rust_args: global_rust_build_args,
    override_options: [uapi_rust_std],
    install: true,
)

libuapirs_dep = declare_dependency(link_with : uapi_rs_lib)
