# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

task_metadata_schema = files(
    'metadata.schema.json.cpp',
)

# forge the JSON schema, using the Kconfig values and the enumerate informations
# in ensure to guarantee the correct values of various fields (max values, enum
# values, etc...)
task_metadata_schema = custom_target(
    'task_metadata_schema',
    input: task_metadata_schema,
    output: '@BASENAME@',
    depfile: '@PLAINNAME@.d',
    command:
        meson.get_compiler('c', native: true).cmd_array() + [
        '-DSCHEMA_GENERATION',
        '-I', join_paths(meson.current_source_dir(), '../../kernel/include'),
        '-I', join_paths(meson.current_source_dir(), '../../uapi/include'),
        '-include', '@0@'.format(kconfig_h),
        '-E', '-P',
        '-MT', '@INPUT@',
        '-MMD', '-MF', '@DEPFILE@',
        '@INPUT@',
        '-o', '@OUTPUT@',
    ],
    build_by_default: true,
)
