subdir('capabilities')
subdir('handles')
subdir('types')

sentry_c_uapi_headers_dep = []
cbindgen_configs = files([
    'capabilities/capability.h.toml',
    'handles/handle.h.toml',
    'types/types.h.toml',
])

foreach cfg: cbindgen_configs
    sentry_c_uapi_headers_dep += declare_dependency(
        sources:
            custom_target(
                input: cfg,
                output: '@BASENAME@',
                depfile: '@BASENAME@.dep',
                command: [cbindgen, meson.project_source_root() / fs.parent(cfg),
                '-c', '@INPUT@',
                '--depfile', '@DEPFILE@',
                '-o', '@OUTPUT@'],
                install: true,
                install_dir: get_option('includedir'),
                install_tag: 'devel',
            )
    )
endforeach

uapi_cargo_toml = files('Cargo.toml')
uapi_headers = files([
    'device.h',
    'handle_defs.h',
    'handle_toolkit.h',
])

foreach header: uapi_headers
    install_headers(fs.relative_to(header, meson.current_source_dir()),
        preserve_path: true,
        follow_symlinks: false,
    )
endforeach


userspace_uapi_include_dir = include_directories('.')
uapi_h = custom_target('uapi_header',
    input: uapi_cbindgen_toml,
    output: 'uapi.h',
    depend_files: [ uapi_rust_libfile, uapi_cargo_toml ],
    depends: [systypes_lib],
    depfile: 'uapi.dep',
    command: [cbindgen, meson.current_source_dir(),
    '-c', '@INPUT@',
    '--depfile', '@DEPFILE@',
    '-o', '@OUTPUT@'],
    install: true,
    install_dir: get_option('includedir'),
    install_tag: 'devel',
)

sentry_c_uapi_headers_dep += declare_dependency(sources: [ uapi_h ])
external_deps += sentry_c_uapi_headers_dep
