subdir('managers_bindings')

sysgate_lib = static_library(
    'sysgate',
    sources : ['lib.rs'],
    dependencies: [systypes_dep, handles_dep, managers_bindings_dep],
    rust_abi: 'c',
    rust_args: global_rust_build_args,
    install: false,
)
sysgate_dep = declare_dependency(link_with: sysgate_lib)

csyscalls = files(
    'sysgate_send_ipc.c',
    'sysgate_send_signal.c',
    'sysgate_waitforevent.c',
    'sysgate_gpio.c',
    'sysgate_get_devhandle.c',
    'sysgate_int_acknowledge.c',
)

sentry_source_set.add(csyscalls)

external_deps += sysgate_dep
