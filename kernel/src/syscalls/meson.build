subdir('managers_bindings')

sysgate_lib = static_library(
    'sysgate',
    sources : ['lib.rs'],
    dependencies: [systypes_dep, managers_bindings_dep],
    rust_abi: 'c',
)
sysgate_dep = declare_dependency(link_with: sysgate_lib)

external_deps += sysgate_dep
