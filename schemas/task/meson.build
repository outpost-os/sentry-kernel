# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

task_metadata_schema = files(
    'metadata.schema.json.cpp',
)

schema_preprocessor = meson.get_compiler('c', native: true)

# forge the JSON schema, using the Kconfig values and the enumerate informations
# in ensure to guarantee the correct values of various fields (max values, enum
# values, etc...)
task_metadata_schema = custom_target(
    'task_metadata_schema',
    input: [ task_metadata_schema ],
    output: '@BASENAME@',
    command: [
        schema_preprocessor.cmd_array(),
        '-DSCHEMA_GENERATION',
        '-I', join_paths(meson.current_source_dir(), '../../kernel/include'),
        '-I', join_paths(meson.current_source_dir(), '../../uapi/include'),
        '-include', '@0@'.format(kconfig_h),
        '-E', '-P',
        task_metadata_schema,
        '-o', '@OUTPUT@',
    ],
    build_by_default: true,
)
