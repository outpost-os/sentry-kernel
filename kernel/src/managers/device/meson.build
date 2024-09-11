# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

mgr_device_files = files(
    'device.c',
)

managers_source_set.add(mgr_device_files)

devices_template_h = files(['devlist-dt.h.in'])
devices_dtsgen_h = dtsgen.process(devices_template_h)
managers_private_gen_header_set.add(devices_dtsgen_h)
