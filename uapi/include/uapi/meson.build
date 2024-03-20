uapi_headers = files([
    'device.h',
    'handle.h',
    'types.h'
])
uapi_h = files(['uapi.h'])

foreach header: uapi_headers
    install_headers(fs.relative_to(header, meson.current_source_dir()),
        preserve_path: true,
        follow_symlinks: false,
    )
endforeach

foreach header: uapi_h
    install_headers(fs.relative_to(header, meson.current_source_dir()),
        preserve_path: true,
        install_dir: get_option('includedir'),
        follow_symlinks: false,
    )
endforeach

userspace_uapi_include_dir = include_directories('.')
