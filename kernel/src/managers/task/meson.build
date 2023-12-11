# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# main kernel-relative content
sentry_source_set.add(files(
  'task_init.c',
  'task_core.c',
  'task_idle.c',
))

if kconfig_data.get('CONFIG_BUILD_TARGET_AUTOTEST', 0) == 1
sentry_source_set.add(files(
  'task_autotest.c',
))
endif
