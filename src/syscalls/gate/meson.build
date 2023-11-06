sysgate_lib = static_library(
    'sysgate',
    sources : ['lib.rs'],
    dependencies: systypes_dep,
    rust_crate_type: 'staticlib',
)
sysgate_dep = declare_dependency(link_with: sysgate_lib)
