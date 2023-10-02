
frama_c = find_program('frama-c', version: '27.1', required: true, native: true)
z3 = find_program('z3', required: true, native: true)
cvc4 = find_program('cvc4', 'cvc4-1.7', required: true, native: true)


framac_gen_opts = [
  '-no-frama-c-stdlib',
  '-kernel-msg-key', 'pp',
  '-kernel-warn-key', 'c11=inactive,parser:unsupported=feedback',
  '-kernel-debug','1',
  '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), 'libsentry-parse-user.log'),
  '-kernel-log','a:'+ join_paths(meson.current_build_dir(), 'libsentry-parse-all.log'),
  '-machdep', 'x86_32',
  '-instantiate',
  '-json-compilation-database', join_paths(meson.build_root(), 'compile_commands.json'),
  '-config', join_paths(meson.current_build_dir(), '.libsentry-config'),
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
 '-eva-log', 'a:'+join_paths(meson.current_build_dir(), 'libsentry-rte-eva.log'),
 '-eva-report-red-statuses', join_paths(meson.current_build_dir(), 'libsentry-red-statuses.log'),
 '-metrics',
]

framac_wp_opts = [
  '-wp',
  '-wp-model', 'Typed+ref+int',
  '-wp-literals',
  '-wp-prover', 'alt-ergo,cvc4,z3,tip',
  '-wp-timeout', '15',
  '-wp-smoke-tests',
  '-wp-time-margin', '25',
  '-wp-no-smoke-dead-code',
  '-wp-no-smoke-dead-call',
  '-wp-log', 'a:'+join_paths(meson.current_build_dir(), 'libsentry-wp.log'),
]

framac_md_opts = [
  '-mdr-gen', 'md',
  '-mdr-out', join_paths(meson.current_build_dir(), 'libsentry-report.md'),
  '-mdr-title', 'Sentry kernel noRTE report',
  '-mdr-log', 'a:'+join_paths(meson.current_build_dir(), 'libsentry-md.log'),
]
#'-wp-prop="-@lemma"',
frama_c_entrypoint = files(
  'main.c',
)

# specify an ELF including framaC main. This forge the correct flags in the
# compile_commands.json so that framaC can use it. Although it should never be
# built by meson, but instead json metadata being used by framaC to forge the
# correct cpp args
framac_stub_elf = executable(
    'framac_main',
    name_suffix: 'elf',
    sources: [frama_c_entrypoint, sentry_source_set_config.sources(), sentry_header_set_config.sources() ],
    include_directories: kernel_inc,
    dependencies: [sentry_dep, external_deps],
    c_args: [ target_arch_args, global_build_args ],
    install: false,
    build_by_default: false,
)


# parsing
frama_c_parsing = custom_target(
    env: {'FRAMAC_SESSIfON': join_paths(meson.current_build_dir(), '.frama-c')},
    command: [
      frama_c,
      frama_c_entrypoint, sentry_source_set_config.sources(),
      framac_gen_opts,
    ],
    capture: false,
    input: [ sentry_header_set_config.sources() ],
    output: 'libsentry.parse',
)
framac_parsing = alias_target('framac_parse', frama_c_parsing)

frama_c_eva = custom_target(
    env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), '.frama-c')},
    command: [
      frama_c,
      frama_c_entrypoint, sentry_source_set_config.sources(),
      framac_gen_opts,
      framac_rte_eva_opts,
      '-save',join_paths(meson.current_build_dir(), 'libsentry.eva'),
      '-then',
      framac_md_opts,
    ],
    capture: false,
    input: [ sentry_header_set_config.sources() ],
    output: 'libsentry.eva',
)
framac_eva = alias_target('framac_eva', frama_c_eva)

frama_c_wp = custom_target(
    env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), '.frama-c')},
    command: [
      frama_c,
      frama_c_entrypoint, sentry_source_set_config.sources(),
      framac_gen_opts,
      framac_rte_eva_opts,
      '-then', framac_wp_opts,
      '-save',join_paths(meson.current_build_dir(), 'libsentry.wp'),
    ],
    capture: false,
    input: [ sentry_header_set_config.sources() ],
    output: 'libsentry.wp',
)
framac_wp = alias_target('framac_wp', frama_c_wp)


#frama_c = custom_target(
#)
