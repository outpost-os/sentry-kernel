# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# Sentry managers list
subdir('security')
subdir('task')
subdir('io')
if kconfig_data.get('CONFIG_BUILD_TARGET_RELEASE', 0) == 0
subdir('debug')
endif
subdir('clock')
subdir('interrupt')
subdir('memory')
subdir('device')
