# specify an ELF including framaC main. This forges the correct flags in the
# compile_commands.json so that framaC can use it. Although it should never be
# built by meson, but instead json metadata being used by framaC to forge the
# correct cpp args
framac_bsp_exti_stub_entrypoint = files(
  'main.c',
)

framac_bsp_exti_stub_elf = executable(
    'framac_bsp_exti_stub_exe',
    name_suffix: 'elf',
    sources: [framac_bsp_exti_stub_entrypoint, sentry_header_set_config.sources() ],
    include_directories: kernel_inc,
    dependencies: [sentry_dep, external_deps],
    c_args: [ target_arch_args, global_build_args ],
    install: false,
    build_by_default: false,
)

test(
  'frama-C-wp-bsp-exti',
  frama_c,
  args: [
    framac_bsp_exti_stub_entrypoint, meson.project_source_root()+'/kernel/src/drivers/exti/stm32-exti.c',
    framac_gen_opts,
    framac_rte_eva_opts,
    '-eva-log', 'a:'+join_paths(meson.current_build_dir(), 'sentry-rte-eva.log'),
    '-eva-report-red-statuses', join_paths(meson.current_build_dir(), 'sentry-red-statuses.log'),
    '-metrics',
    '-metrics-eva-cover',meson.project_source_root()+'/kernel/src/drivers/exti/stm32-exti.c',
    '-then', framac_wp_opts,
    '-wp-fct', 'exti_probe,exti_mask_interrupt,exti_unmask_interrupt,exti_mask_event,exti_unmask_event,exti_generate_swinterrupt,exti_clear_pending',
    '-wp-log', 'a:'+join_paths(meson.current_build_dir(), 'sentry-wp.log'),
    '-save',join_paths(meson.current_build_dir(), 'sentry-bsp-exti.wp'),
    '-then',
    framac_md_opts,
  ],
  env: {'FRAMAC_SESSIfON': join_paths(meson.current_build_dir(), '.frama-c')},
  depends: [ framac_dep ],
  suite: 'proof',
  timeout: 1200,
)
