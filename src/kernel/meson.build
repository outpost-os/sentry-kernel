# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# scheduling part
sentry_source_set.add(files(
  'sched/rrmq.c',
  'sched/fifo.c',
  'sched/sched.c'
))

# main kernel-relative content
sentry_source_set.add(files(
  'kworker.c',
  'task.c',
))

# entrypoint is out of the libsentry
sentry_entry = files(
  'entrypoint.c'
)
