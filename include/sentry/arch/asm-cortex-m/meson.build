# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# list of statically defined headers
sentry_header_set.add(files(
    'io.h',
    'membarriers.h',
    'mpu.h',
    'mpu_pmsa_v7.h',
    'nvic.h',
    'platform.h',
    'scb.h',
    'soc.h',
    'system.h',
    'systick.h',
    'thread.h',
))

irq_defs_in = files('irq_defs.h.in')
# generated headers
irq_def_h = custom_target('gen_irq_defs',
   input: irq_defs_in,
    output: '@BASENAME@',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

layout_h = custom_target('gen_layout',
    input: layout_in,
    output: '@BASENAME@',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

core_in = files('core.h.in')

core_h = custom_target('gen_core',
    input: core_in,
    output: '@BASENAME@',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

# the way we generate the buses list depend on the SoC familly. To do
# that, the input jinja template is selected depending on the configured SOC
# familly or subfamilly
buses_h_in_set = ssmod.source_set()
buses_h_in_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: files('stm32-buses.h.in'))
# here, we can add other templates for other ARM SoC famillies if needed
buses_h_in_set_config = buses_h_in_set.apply(kconfig_data, strict: false)

buses_h = custom_target('gen_buses',
    input: buses_h_in_set_config.sources(),
    output: 'buses.h',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME', 'RCC', '@INPUT@' ],
)

sentry_header_set.add(
    irq_def_h.to_list(),
    layout_h.to_list(),
    core_h.to_list(),
    buses_h.to_list(),
)
