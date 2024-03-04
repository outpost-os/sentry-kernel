# This is a list of dict
uapi_cbindgen_configs = []
uapi_cbindgen_headers = []

subdir('handles')
subdir('types')

foreach cfg: uapi_cbindgen_configs
    _toml = cfg['toml']
    _depend_files = cfg['depend_files']
    _depends = cfg['depends']
    uapi_cbindgen_headers += custom_target(
        input: _toml,
        output: '@BASENAME@',
        depfile: '@BASENAME@.dep',
        depend_files: _depend_files,
        depends: _depends,
        command: [cbindgen, meson.global_source_root() / fs.parent(_toml),
        '-c', '@INPUT@',
        '--depfile', '@DEPFILE@',
        '-o', '@OUTPUT@'],
        install: true,
        install_dir: get_option('includedir'),
        install_tag: 'devel',
    )
endforeach

uapi_cargo_toml = files('Cargo.toml')
uapi_headers = files([
    'device.h',
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
    depends: [uapi_cbindgen_headers], # XXX: Add uapi_rs deps, break circular dep here
    depfile: 'uapi.dep',
    command: [cbindgen, meson.current_source_dir(),
    '-c', '@INPUT@',
    '--depfile', '@DEPFILE@',
    '-o', '@OUTPUT@'],
    install: true,
    install_dir: get_option('includedir'),
    install_tag: 'devel',
)

sentry_c_uapi_headers_dep = declare_dependency(sources: [uapi_cbindgen_headers, uapi_h])
external_deps += sentry_c_uapi_headers_dep
