# specify an ELF including framaC main. This forges the correct flags in the
# compile_commands.json so that framaC can use it. Although it should never be
# built by meson, but instead json metadata being used by framaC to forge the
# correct cpp args
framac_bsp_rcc_stub_entrypoint = files(
  'main.c',
)

framac_bsp_rcc_stub_elf = executable(
    'framac_bsp_rcc_stub_exe',
    name_suffix: 'elf',
    sources: [framac_bsp_rcc_stub_entrypoint, sentry_header_set_config.sources() ],
    include_directories: kernel_inc,
    dependencies: [sentry_dep, external_deps ],
    c_args: [ target_arch_args, global_build_args ],
    install: false,
    build_by_default: false,
)

test(
  'frama-C-wp-bsp-rcc',
  frama_c,
  args: [
    framac_bsp_rcc_stub_entrypoint,
    meson.global_build_root() / 'src/libsentry.a.p/stm32-rcc.c',
    framac_gen_opts,
    framac_rte_eva_opts,
    '-eva-log', 'a:'+join_paths(meson.current_build_dir(), 'sentry-rte-eva.log'),
    '-eva-report-red-statuses', join_paths(meson.current_build_dir(), 'sentry-red-statuses.log'),
    '-metrics',
    '-metrics-eva-cover',meson.global_build_root() / 'src/libsentry.a.p/stm32-rcc.c',
    '-then', framac_wp_opts,
    '-wp-fct','rcc_probe,rcc_get_core_frequency,rcc_enable_apbx,rcc_disable_apbx,rcc_enable,rcc_disable,rcc_get_bus_clock',
    '-wp-log', 'a:'+join_paths(meson.current_build_dir(), 'sentry-wp.log'),
    '-save',join_paths(meson.current_build_dir(), 'sentry-bsp-rcc.wp'),
    '-then',
    framac_md_opts,
  ],
  env: {'FRAMAC_SESSIfON': join_paths(meson.current_build_dir(), '.frama-c')},
  depends: [ framac_dep ],
  suite: 'proof',
  timeout: 1200,
)
