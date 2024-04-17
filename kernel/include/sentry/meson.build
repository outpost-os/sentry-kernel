# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

subdir('arch')

# list of statically defined headers: generic kernel headers
sentry_header_set.add(files(
  'bits.h',
  'dma.h',
  'handle.h',
  'io.h',
  'ipc.h',
  'job.h',
  'ktypes.h',
  'sched.h',
  'thread.h',
))

subdir('managers')

# zlib headers
sentry_header_set.add(files(
  'zlib/crypto.h',
  'zlib/math.h',
  'zlib/sort.h',
))
