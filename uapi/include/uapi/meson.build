# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

uapi_headers = files([
    'device.h',
    'handle.h',
    'types.h',
    'dma.h',
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

platform_h = configure_file(input : 'platform.h.in',
               output : 'platform.h',
               configuration : kconfig_data)

install_headers(platform_h,
        preserve_path: true,
        install_dir: get_option('includedir'),
        follow_symlinks: false,
    )

userspace_uapi_include_dir = include_directories('.')
