# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

autotest_inc = include_directories('.')

devices_template_h = files(['devices-dt.h.in'])
devices_dtsgen_h = dtsgen.process(devices_template_h)

shm_template_h = files(['shms-dt.h.in'])
shm_dtsgen_h = dtsgen.process(shm_template_h)

autotest_headers = files(
    'testlib/assert.h',
    'testlib/log.h',
)
