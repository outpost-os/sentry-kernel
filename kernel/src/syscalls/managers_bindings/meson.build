rust = import('rust')

managers_bindings = rust.bindgen(
    input : ['managers_meta.h'],
    output : 'managers_bindings.rs',
    include_directories : include_directories(
        '../../../include',
        '../../../include/sentry/arch/asm-cortex-m',
        '../../../../uapi/include',
        '../../../../uapi/include/uapi',
    ),
    args : ['--use-core',
            '--raw-line', '#![no_std]',
            '--raw-line', '#![allow(nonstandard_style)]',
            '--raw-line', 'use systypes::*;',
            '--no-layout-tests',
            '--merge-extern-blocks',
            '--blocklist-type','([a-z]+h_t)',
            '--blocklist-function','(strtod)',
            '--blocklist-function','(strtold)',
            '--blocklist-function','(qecvt)',
            '--blocklist-function','(qfcvt)',
            '--blocklist-function','(qgcvt)',
            '--blocklist-function','(qecvt_r)',
            '--blocklist-function','(qfcvt_r)',
            ],
    c_args : [
        global_build_args,
        '-D__arm__',
    ],
    dependencies : [cmsis_dep, external_deps, declare_dependency(sources: core_h)],
)
managers_bindings_lib = static_library(
    'managers_bindings',
    sources : [managers_bindings],
    dependencies : [systypes_dep],
)
managers_bindings_dep = declare_dependency(link_with: managers_bindings_lib)
