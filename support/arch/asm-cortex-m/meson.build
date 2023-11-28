# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

target_arch_args += [
    '-mcpu=cortex-@0@'.format(kconfig_data.get_unquoted('CONFIG_ARCH_ARM_CORTEX_NAME')),
    kconfig_data.get_unquoted('CONFIG_ISA_CFLAGS'),
    kconfig_data.get_unquoted('CONFIG_ENDIANNESS_CFLAGS'),
    kconfig_data.get_unquoted('CONFIG_FPU_ABI_CFLAGS'),
]

if kconfig_data.get('CONFIG_FPU_SOFT_ABI', 0) != 1
target_arch_args += [
    kconfig_data.get_unquoted('CONFIG_FPU_CFLAGS'),
]
endif
