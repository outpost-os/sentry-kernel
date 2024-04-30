# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

task_metadata_json = files('task_metadata.json')
task_capabilities_json = files('task_capabilities.json')

# TODO:
# task_metadata_schema = files('task_metadata.schema.json')
# package_metadata_schema = files('package_metadata.schema.json')
#
# Add a run_target that validate task_metadata.json
# [...]

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
        '-include', join_paths(fs.parent(kconfig_h),fs.name(kconfig_h)),
        '-nostdinc', '-undef',
        '-E', '-P',
        '-MT', '@INPUT@',
        '-MMD', '-MF', '@DEPFILE@',
        '@INPUT@',
        '-o', '@OUTPUT@',
    ],
    install: true,
    install_dir:  get_option('datadir') / meson.project_name(),
    install_tag: 'bin-devel',
)
