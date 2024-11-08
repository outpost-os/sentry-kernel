# SPDX-FileCopyrightText: 2023 - 2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

target_cpu = 'cortex-@0@'.format(kconfig_data.get_unquoted('CONFIG_ARCH_ARM_CORTEX_NAME'))
target_use_fpu = kconfig_data.get('CONFIG_FPU_SOFT_ABI', 0) != 1

target_rustargs = [
    '--target=@0@'.format(kconfig_data.get_unquoted('CONFIG_RUSTC_TARGET')),
    '-Ctarget-cpu='+ target_cpu,
]

target_cflags = [
    '-mcpu=' + target_cpu,
    kconfig_data.get_unquoted('CONFIG_ISA_CFLAGS'),
    kconfig_data.get_unquoted('CONFIG_ENDIANNESS_CFLAGS'),
    kconfig_data.get_unquoted('CONFIG_FPU_ABI_CFLAGS'),
]

# Set correct compiler flags for gcc and rustc according to FPU usage and float ABI
#
# For C, append FPU cflags if FPU used, this flags is set by kconfig.
# For Rust:
#  - kconfig set correct arch if hard float is required.
#  - As target-cpu is set, if target has cpu, it is used (ABI depends on target triple
#    w/ or w/o hf suffix. This is set by kconfig dependencies too.
#  - In the case of float software emulation on target w/ FPU, one has to add `soft-float`
#    to `target-features` compile options
if target_use_fpu
target_cflags += [kconfig_data.get_unquoted('CONFIG_FPU_CFLAGS')]
else
target_rustargs += [ '-Ctarget-features=+soft-float' ]
endif

target_arch_args += target_cflags


summary(
    {
        'cflags': target_cflags,
        'rustargs': target_rustargs,
    },
    bool_yn: true,
    section: 'Target specific compile args'
)
