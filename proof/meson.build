
frama_c = find_program('frama-c', version: '27.1', required: true, native: true)
z3 = find_program('z3', required: true, native: true)
cvc4 = find_program('cvc4', 'cvc4-1.7', required: true, native: true)

sentry_includedirs = [
  '-I' + top_dir + '/include/sentry/arch/asm-cortex-m',
  '-I' + top_dir + '/src/drivers/syscfg',
  '-I' + top_dir + '/src/drivers/exti',
  '-I' + top_dir + '/src/libsentry.a.p',
  '-I' + top_dir + '/src/drivers/gpio',
  '-I' + top_dir + '/src/drivers/rng',
  '-I' + top_dir + '/include',
  '-I' + top_dir + '/src',
  '-I.',
  '-I..',
  '-I' + top_dir + '/src/drivers/clk',
  '-I' + top_dir + '/subprojects/cmsis/include',
]

framac_gen_opts = [
  '-no-frama-c-stdlib',
  '-kernel-msg-key', 'pp',
  '-kernel-warn-key', 'c11=inactive,parser:unsupported=feedback',
  '-kernel-debug','1',
  '-kernel-log','iu:'+ join_paths(meson.current_build_dir(), 'parse-user.log'),
  '-kernel-log','a:'+ join_paths(meson.current_build_dir(), 'parse-all.log'),
  '-machdep', 'x86_32',
  '-instantiate',
  '-json-compilation-database', join_paths(meson.build_root(), 'compile_commands.json'),
  '-config', join_paths(meson.current_build_dir(), '.frama-c-config'),
  '-cpp-extra-args-per-file', meson.current_source_dir() + '/main.c:'+'-include @0@'.format(kconfig_h)+' -ffreestanding -fno-builtin -nostdlib -fno-common -std=gnu11 '+' '.join(sentry_includedirs),
  '-cpp-extra-args=-nostdinc',
  '-frama-c-stdlib',
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
 '-eva-log', join_paths(meson.current_build_dir(), 'frama-c-rte-eva.log'),
 '-eva-report-red-statuses', join_paths(meson.current_build_dir(), 'frama-c-rte-eva-red-statuses.log'),
 '-metrics',
]

framac_wp_opts = [
  '-wp',
  '-wp-dynamic',
  '-wp-model', 'Typed+ref+int',
  '-wp-literals',
  '-wp-prover', 'alt-ergo,cvc4,z3,tip',
  '-wp-timeout', '15',
  '-wp-smoke-tests',
  '-wp-prop="-@lemma"',
  '-wp-time-margin', '25',
  '-wp-no-smoke-dead-code',
  '-wp-no-smoke-dead-call',
  '-wp-log', join_paths(meson.current_build_dir(), 'frama-c-wp.log'),
]

frama_c_entrypoint = files(
  'main.c',
)

frama_c_parsing = custom_target(
    env: {'FRAMAC_SESSION': join_paths(meson.current_build_dir(), '.frama-c')},
    command: [ frama_c, frama_c_entrypoint, sentry_source_set_config.sources(), framac_gen_opts ],
    capture: false,
    output: 'frama-c.parse',
)
framac_parsing = alias_target('framac_parsing', frama_c_parsing)

#frama_c = custom_target(
#)
