# specify an ELF including framaC main. This forges the correct flags in the
# compile_commands.json so that framaC can use it. Although it should never be
# built by meson, but instead json metadata being used by framaC to forge the
# correct cpp args
# this allows custom entrypoint for, typically, syscall entrypoints coverage
frama_c_norte_gate_get_prochandle_entrypoint = files(
  'handler.c',
)

framac_stub_elf = executable(
    'framac_norte_systick_entrypoint',
    name_suffix: 'elf',
    sources: [ frama_c_norte_gate_get_prochandle_entrypoint ],
    include_directories: kernel_inc,
    dependencies: [sentry_dep, external_deps],
    c_args: [ target_arch_args, global_build_args, sentry_dts_args ],
    install: false,
    build_by_default: false,
)

# testing EVA/noRTE through kernel svc handler
test(
  'frama-c-eva-handler-gate-get-prochandle',
 frama_c,
 args: [
    frama_c_norte_gate_get_prochandle_entrypoint, sentry_source_set_config.sources(),
    framac_gen_opts,
    '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), 'frama-c-eva-handler-gate-get_prochandle-user.log'),
    '-kernel-log','a:'+ join_paths(meson.current_build_dir(), 'frama-c-eva-handler-gate-get_prochandle-all.log'),
    '-main', 'handler_entrypoint',
    framac_rte_eva_opts,
    '-eva-flamegraph',join_paths(meson.current_build_dir(), 'frama-c-eva-handler-gate-get_prochandle.flamegraph'),
    '-eva-report-red-statuses',join_paths(meson.current_build_dir(), 'frama-c-eva-handler-gate-get_prochandle.red'),
    '-metrics',
    '-metrics-eva-cover',
    '-metrics-output',join_paths(meson.current_build_dir(), 'frama-c-eva-handler-gate-get_prochandle.json'),
    '-save',join_paths(meson.current_build_dir(), 'frama-c-eva-handler-gate-get_prochandle.session'),
    '-then',
    framac_md_opts,
    '-mdr-out', join_paths(meson.current_build_dir(), 'frama-c-eva-handler-gate-get_prochandle-report.md'),
    '-mdr-log', 'a:'+join_paths(meson.current_build_dir(), 'frama-c-eva-handler-gate-get_prochandle-md.log'),
  ],
  env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), 'frama-c-eva-handler-gate-get_prochandle')},
  depends: [ framac_dep ],
  suite: 'proof',
  timeout: 600,
  is_parallel: false,
  priority: 254,
)

test(
  'frama-c-eva-handler-gate-get-prochandle-redalarm',
  py3,
  args: [
    '-c',
    redalarmcount_py_wrapper,
    join_paths(meson.current_build_dir(), 'frama-c-eva-handler-gate-get_prochandle.red'),
  ],
  depends: [ framac_dep ],
  suite: 'proof',
  should_fail: true,
  is_parallel: false,
  priority: 253,
)
