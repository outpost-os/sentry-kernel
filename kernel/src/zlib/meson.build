# sentry zlib
zlib_files = files()

subdir('crypto')

zlib_files += files(
    'string.c',
)

zlib_source_set = ssmod.source_set()
zlib_source_set.add(zlib_files)
zlib_source_set_config = zlib_source_set.apply(kconfig_data, strict: false)


sentry_zlib_lib = static_library('sentry_zlib',
    sources: [
        zlib_source_set_config.sources(),
    ],
    include_directories: kernel_inc,
    c_args: [ target_arch_args, global_build_args ],
    install: false,
    dependencies: [zlib_source_set_config.dependencies(), external_deps],
)

sentry_zlib_dep = declare_dependency(
    link_with: sentry_zlib_lib,
    include_directories: kernel_inc,
)
