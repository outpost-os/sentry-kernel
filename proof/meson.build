
frama_c = find_program('frama-c', version: '27.1', required: true, native: true)
z3 = find_program('z3', required: true, native: true)
cvc4 = find_program('cvc4', 'cvc4-1.7', required: true, native: true)


framac_gen_opts = [
  '-no-meta',
  '-kernel-msg-key', 'pp',
  '-kernel-warn-key', 'c11=inactive,parser:unsupported=feedback',
  '-kernel-debug','1',
  '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), 'sentry-parse-user.log'),
  '-kernel-log','a:'+ join_paths(meson.current_build_dir(), 'sentry-parse-all.log'),
  '-machdep', 'x86_32',
  '-instantiate',
  '-json-compilation-database', join_paths(meson.project_build_root(), 'compile_commands.json'),
  '-config', join_paths(meson.current_build_dir(), '.sentry-config'),
  '-cpp-extra-args=-nostdinc',
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
  '-mdr-out', join_paths(meson.current_build_dir(), 'sentry-report.md'),
  '-mdr-title', 'Sentry kernel noRTE report',
  '-mdr-log', 'a:'+join_paths(meson.current_build_dir(), 'sentry-md.log'),
]
#'-wp-prop="-@lemma"',
kernel_entrypoint = files(
  '../src/core/entrypoint.c',
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
    input: [ sentry_header_set_config.sources() ],
    output: 'framac.dep',
)

#test(
#  'frama-C-parsing',
#  frama_c,
#  args: [
#    kernel_entrypoint, sentry_source_set_config.sources(),
#    framac_gen_opts,
#    '-main', '_entrypoint',
#  ],
#  env: {'FRAMAC_SESSIfON': join_paths(meson.current_build_dir(), '.frama-c')},
#  suite: 'proof',
#  depends: [ framac_dep ],
#  timeout: 60,
#  is_parallel: false,
#  priority: 255,
#  should_fail: true, # XXX until dts-gen sources parse and eva fixup
#)

#test(
#  'frama-C-eva',
# frama_c,
# args: [
#    kernel_entrypoint, sentry_source_set_config.sources(),
#    framac_gen_opts,
#    '-main', '_entrypoint',
#    framac_rte_eva_opts,
#    '-metrics',
#    '-metrics-eva-cover',
#    '-metrics-output',join_paths(meson.current_build_dir(), 'sentry-rte-eva-coverage.json'),
#    '-save',join_paths(meson.current_build_dir(), 'sentry.eva'),
#    '-then',
#    framac_md_opts,
#  ],
#  env: {'FRAMAC_SESSIfON': join_paths(meson.current_build_dir(), '.frama-c')},
#  depends: [ framac_dep ],
#  suite: 'proof',
#  timeout: 120,
#  is_parallel: false,
#  priority: 254,
#  should_fail: true, # XXX until dts-gen sources parse and eva fixup
#)

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
subdir('proof_bsp')
# TODO
