rust = import('rust')

bindgen_cross_flags = []
if meson.is_cross_build()
    bindgen_cross_flags += meson.get_external_property(
        'bindgen_clang_arguments',
        [],
    )
endif

managers_bindings = rust.bindgen(
    input : ['managers_meta.h'],
    output : 'managers_bindings.rs',
    include_directories : include_directories(
        '../../../include',
        '../../../include/sentry/arch/asm-cortex-m',
        '../../../../uapi/include',
    ),
    args : ['--use-core',
            '--raw-line', '#![no_std]',
            '--raw-line', '#![allow(nonstandard_style)]',
            '--merge-extern-blocks'],
    c_args : [bindgen_cross_flags, global_build_args],
    dependencies : [cmsis_dep, declare_dependency(sources: core_h)],
)
managers_bindings_lib = static_library(
    'managers_bindings',
    sources : [managers_bindings],
)
managers_bindings_dep = declare_dependency(link_with: managers_bindings_lib)
