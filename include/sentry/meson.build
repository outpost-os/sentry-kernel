# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

subdir('arch')

# list of statically defined headers: generic kernel headers
sentry_header_set.add(files(
  'bits.h',
  'dma.h',
  'io.h',
  'ipc.h',
  'ktypes.h',
  'mm.h',
  'signal.h',
  'thread.h',
))

# managers headers
sentry_header_set.add(files(
  'managers/io.h',
  'managers/debug.h',
  'managers/device.h',
))
