# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: LicenseRef-LEDGER

pymod = import('python')
sphinx = find_program('sphinx-build')
doxygen = find_program('doxygen')
py3 = pymod.find_installation('python3', modules: ['exhale','sphinx_rtd_theme'])

api_rst = files(
    'sphinx/build_system/targets.rst',
    'sphinx/build_system/svd.rst',
    'sphinx/build_system/index.rst',
    'sphinx/build_system/dts.rst',
    'sphinx/concepts/archi_req.rst',
    'sphinx/concepts/security.rst',
    'sphinx/concepts/index.rst',
    'sphinx/concepts/initial.rst',
    'sphinx/index.rst',
    'sphinx/deps.rst',
    'sphinx/sw_architecture/asp.rst',
    'sphinx/sw_architecture/bsp.rst',
    'sphinx/sw_architecture/syscalls.rst',
    'sphinx/sw_architecture/index.rst',
)
api = custom_target('sphinx-doc',
    input: api_rst,
    depend_files: [files('sphinx/conf.py')],
    output: 'full',
    command: [sphinx, '-b', 'html', '-q', '-d',
        'build/doctrees',
        '-Dversion=' + meson.project_version(),
        meson.current_source_dir() / 'sphinx',
        'doc/full',
    ])
doc = alias_target('doc', api)
