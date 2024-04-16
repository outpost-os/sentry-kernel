# SPDX-FileCopyrightText: 2024 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

add_languages('cpp', native: true, required: true)

nl_json = subproject('nlohmann_json')
nl_json_dep = nl_json.get_variable('nlohmann_json_dep')

genmetadata_deps = [ nl_json_dep ]

subdir('src')

genmetadata = executable(
    'genmetadata',
    genmetadata_src,
    link_language: 'cpp',
    dependencies: genmetadata_deps,
    install: false,
    build_by_default: true,
    install_dir: get_option('libexecdir'),
    native: true,
)
