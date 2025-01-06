# SPDX-FileCopyrightText: 2023 - 2025 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

autotest_inc = include_directories('.')

autotest_headerset.add(
    files(
        'testlib/assert.h',
        'testlib/log.h',
    )
)

devices_template_h = files(['devices-dt.h.in'])
devices_dtsgen_h = dtsgen.process(devices_template_h)
autotest_headerset.add(when: 'CONFIG_TEST_DEVICES', if_true: devices_dtsgen_h)

shm_template_h = files(['shms-dt.h.in'])
shm_dtsgen_h = dtsgen.process(shm_template_h)
autotest_headerset.add(when: 'CONFIG_TEST_SHM', if_true: shm_dtsgen_h)
