cbindgen = find_program('cbindgen')

# UAPI header generation is always required
subdir('include/uapi')


if with_uapi_opt or with_idle_opt
subdir('src')
endif

uapi_headers = custom_target('uapi_header',
    input: ['cbindgen.toml', 'src/lib.rs', systypes_lib],
    output: 'uapi.dep',
    command: [cbindgen, meson.current_source_dir(),
    '-c', '@INPUT0@',
    '--depfile', '@OUTPUT@',
    '-o', 'uapi/include/uapi/uapi.h'],
)
sentry_c_uapi_headers_dep = declare_dependency(
    sources: [ uapi_headers ],
)

if with_uapi_opt or with_idle_opt
# XXX:
#  This deps is designed for userspace (libshied) only
#  As in linux kernel, uapi headers are not used w/ a kernel name and/or uapi
#  prefix. So, add the uapi include subdir in "include_directories".
sentry_c_uapi_dep = declare_dependency(
    link_with: uapi_rs_lib,
    sources: [ uapi_headers ],
    dependencies: [ libuapirs_dep ],
    compile_args: [ global_build_args, target_arch_args ],
)
endif
