# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

sched_header_set = ssmod.source_set()
zlib_header_set = ssmod.source_set()

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
zlib_header_set.add(files(
  'zlib/crypto.h',
  'zlib/math.h',
  'zlib/sort.h',
))

sched_header_set.add(files(
  'sched.h',
))

sched_header_set_config = sched_header_set.apply(kconfig_data, strict:false)
zlib_header_set_config = zlib_header_set.apply(kconfig_data, strict:false)
