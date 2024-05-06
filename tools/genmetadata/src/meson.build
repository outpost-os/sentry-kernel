# SPDX-FileCopyrightText: 2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

genmetadata_src = files(
    'main.cpp',
)

task_meta_hpp = custom_target('task_meta_hpp',
    input: files('task_meta.hpp.in'),
    output: '@BASENAME@',
    depend_files: [ task_metadata_json ],
    command: [ jinja_cli, '-d', task_metadata_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

capability_hpp = custom_target('capability_hpp',
    input: files('capability.hpp.in'),
    output: '@BASENAME@',
    depend_files: [ task_capabilities_json ],
    command: [ jinja_cli, '-d', task_capabilities_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

genmetadata_src += [task_meta_hpp, capability_hpp]
