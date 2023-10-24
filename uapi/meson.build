cbindgen = find_program('cbindgen')

subdir('src')

uapi_headers = custom_target('uapi_header',
    input: ['cbindgen.toml', 'src/lib.rs', systypes_lib],
    output: 'uapi.h',
    command: [cbindgen, meson.current_source_dir(), '-c', '@INPUT0@', '-o', '@OUTPUT@'],
    build_always: true
)
