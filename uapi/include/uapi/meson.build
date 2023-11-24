
cbindgen = find_program('cbindgen')

subdir('types')

userspace_uapi_include_dir = include_directories('.')

uapi_cbindgen_toml = files('cbindgen.toml')
uapi_cargo_toml = files('Cargo.toml')

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
)
sentry_c_uapi_headers_dep = declare_dependency(
    sources: [ uapi_h ],
)
