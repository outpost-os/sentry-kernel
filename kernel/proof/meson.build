
frama_c = find_program('frama-c', required: true, native: true)
z3 = find_program('z3', required: true, native: true)
cvc4 = find_program('cvc4', 'cvc4-1.8', required: true, native: true)


framac_gen_opts = [
  '-kernel-msg-key', 'pp',
  '-kernel-warn-key', 'c11=inactive,parser:unsupported=feedback',
  '-kernel-debug','1',
  '-machdep', 'gcc_x86_32',
  '-instantiate',
  '-json-compilation-database', join_paths(meson.project_build_root(), 'compile_commands.json'),
  '-config', join_paths(meson.current_build_dir(), '.sentry-config'),
  '-cpp-extra-args=-nostdinc,-DDTS_FILE=\\"@0@\\"'.format(sentry_dts_file),
  '-frama-c-stdlib',
  '-absolute-valid-range', '40000000-0xE000F000',
]

framac_rte_eva_opts = [
 '-rte',
 '-warn-left-shift-negative',
 '-warn-right-shift-negative',
 '-warn-signed-downcast',
 '-warn-signed-overflow',
 '-warn-unsigned-downcast',
 '-warn-unsigned-overflow',
 '-warn-invalid-pointer',
 '-eva',
 '-eva-show-perf',
 '-eva-slevel', '500',
 '-eva-split-limit', '256',
 '-eva-domains', 'symbolic-locations',
 '-eva-domains', 'equality',
 '-eva-split-return', 'auto',
 '-eva-partition-history', '1',
]

framac_wp_opts = [
  '-wp',
  '-wp-model', 'Typed+ref+int',
  '-wp-literals',
  '-wp-timeout', '15',
  '-wp-smoke-tests',
  '-wp-prover','altergo,tip',
  '-wp-time-margin', '25',
  '-wp-no-smoke-dead-code',
  '-wp-no-smoke-dead-call',
]

framac_md_opts = [
  '-mdr-gen', 'md',
  '-mdr-title', 'Sentry kernel noRTE report',
]
#'-wp-prop="-@lemma"',
kernel_entrypoint = files(
  join_paths(meson.project_source_root(), 'kernel/src/startup/entrypoint.c'),
)

# Part 1: analysis from kernel entrypoint. These targets check the call graph from
# the kernel entrypoint itelf, analysing the overall init sequence of the kernel.
# Here, all the probing, platform initialization, etc. is executed through the
# real kernel entrypoint

# overall kernel generated headers must be made before testing
# Although, they are not passed to framaC directly, which get back sources but not
# headers themselves
framac_dep = custom_target(
    command: [ 'true' ],
    input: [
      sentry_header_set_config.sources(),
      sentry_private_header_set_config.sources(),
      sentry_private_gen_header_set_config.sources(),
    ],
    output: 'framac.dep',
)

test(
  'frama-C-parsing',
  frama_c,
  args: [
    kernel_entrypoint, sentry_source_set_config.sources(),
    framac_gen_opts,
    '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), 'frama-c-parsing-user.log'),
    '-kernel-log','a:'+ join_paths(meson.current_build_dir(), 'frama-c-parsing-sentry-all.log'),
    '-main', '_entrypoint',
  ],
  env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), 'frama-c-parsing')},
  suite: 'proof',
  depends: [ framac_dep ],
  timeout: 120,
  is_parallel: false,
  priority: 255,
)

# testing EVA/noRTE through kernel bootup entrypoint (init phase)
test(
  'frama-C-eva',
 frama_c,
 args: [
    kernel_entrypoint, sentry_source_set_config.sources(),
    framac_gen_opts,
    '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), 'frama-c-eva-user.log'),
    '-kernel-log','a:'+ join_paths(meson.current_build_dir(), 'frama-c-eva-all.log'),
    '-main', '_entrypoint',
    framac_rte_eva_opts,
    '-eva-flamegraph',join_paths(meson.current_build_dir(), 'frama-c-eva.flamegraph'),
    '-eva-report-red-statuses',join_paths(meson.current_build_dir(), 'frama-c-eva.red'),
    '-metrics',
    '-metrics-eva-cover',
    '-metrics-output',join_paths(meson.current_build_dir(), 'frama-c-eva-coverage.json'),
    '-save',join_paths(meson.current_build_dir(), 'frama-c-eva.session'),
    '-then',
    framac_md_opts,
    '-mdr-out', join_paths(meson.current_build_dir(), 'frama-c-eva-report.md'),
    '-mdr-log', 'a:'+join_paths(meson.current_build_dir(), 'frama-c-eva-md.log'),
  ],
  env: {'FRAMAC_SESSIfON': join_paths(meson.current_build_dir(), 'frama-c-eva')},
  depends: [ framac_dep ],
  suite: 'proof',
  timeout: 600,
  is_parallel: false,
  priority: 254,
)

# specify an ELF including framaC main. This forges the correct flags in the
# compile_commands.json so that framaC can use it. Although it should never be
# built by meson, but instead json metadata being used by framaC to forge the
# correct cpp args
# this allows custom entrypoint for, typically, syscall entrypoints coverage
frama_c_norte_svc_entrypoint = files(
  'svc_entrypoint.c',
)

framac_stub_elf = executable(
    'framac_norte_svc_entrypoint',
    name_suffix: 'elf',
    sources: [frama_c_norte_svc_entrypoint ],
    include_directories: kernel_inc,
    dependencies: [sentry_dep, external_deps],
    c_args: [ target_arch_args, global_build_args, sentry_dts_args ],
    install: false,
    build_by_default: false,
)

# testing EVA/noRTE through kernel svc handler
test(
  'frama-C-eva-svc',
 frama_c,
 args: [
    frama_c_norte_svc_entrypoint, sentry_source_set_config.sources(),
    framac_gen_opts,
    '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), 'frama-c-eva-svc-user.log'),
    '-kernel-log','a:'+ join_paths(meson.current_build_dir(), 'frama-c-eva-svc-all.log'),
    '-main', 'svc_entrypoint',
    framac_rte_eva_opts,
    '-eva-flamegraph',join_paths(meson.current_build_dir(), 'frama-c-eva-svc.flamegraph'),
    '-eva-report-red-statuses',join_paths(meson.current_build_dir(), 'frama-c-eva-svc.red'),
    '-metrics',
    '-metrics-eva-cover',
    '-metrics-output',join_paths(meson.current_build_dir(), 'frama-c-eva-svc-coverage.json'),
    '-save',join_paths(meson.current_build_dir(), 'frama-c-eva-svc.session'),
    '-then',
    framac_md_opts,
    '-mdr-out', join_paths(meson.current_build_dir(), 'frama-c-eva-svc-report.md'),
    '-mdr-log', 'a:'+join_paths(meson.current_build_dir(), 'frama-c-eva-svc-md.log'),
  ],
  env: {'FRAMAC_SESSIfON': join_paths(meson.current_build_dir(), 'frama-c-eva-svc')},
  depends: [ framac_dep ],
  suite: 'proof',
  timeout: 600,
  is_parallel: false,
  priority: 254,
)


# the bellow part is to be fixed with separated test suites
#frama_c_wp = custom_target(
#    env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), '.frama-c')},
#    command: [
#      frama_c,
#      kernel_entrypoint, sentry_source_set_config.sources(),
#      framac_gen_opts,
#      '-main', '_entrypoint',
#      framac_rte_eva_opts,
#      '-then', framac_wp_opts,
#      '-save',join_paths(meson.current_build_dir(), 'sentry.wp'),
#    ],
#    capture: false,
#    input: [ sentry_header_set_config.sources() ],
#    output: 'sentry.wp',
#)
#framac_wp = alias_target('framac_wp', frama_c_wp)


# Part 2: analysis from Handler entrypoints. These targets check the call graph from
# the interrupts handlers. This check analysis the various call graphs of the interrupts
# execution, using the root Handler as entrypoint source.

# including per driver WP coverage
#subdir('proof_bsp')
# TODO
