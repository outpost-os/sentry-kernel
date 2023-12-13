rust = import('rust')

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
            '--with-derive-default',
            '--merge-extern-blocks'],
    c_args : [global_build_args],
    dependencies : [cmsis_dep, external_deps, declare_dependency(sources: core_h)],
)
managers_bindings_lib = static_library(
    'managers_bindings',
    sources : [managers_bindings],
)
managers_bindings_dep = declare_dependency(link_with: managers_bindings_lib)
