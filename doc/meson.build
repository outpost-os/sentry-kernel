# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: LicenseRef-LEDGER

pymod = import('python')
sphinx = find_program('sphinx-build')
doxygen = find_program('doxygen')
py3 = pymod.find_installation(
    'python3',
    modules: [
        'exhale',
        'sphinx_rtd_theme',
        'weasyprint',
        'sphinx',
        'sphinx_simplepdf',
    ]
    )

concepts_rst = files(
    'concepts/_static/figures/capabilities.png',
    'concepts/_static/figures/outpost.ico',
    'concepts/_static/figures/outpost.png',
    'concepts/build_system/targets.rst',
    'concepts/build_system/svd.rst',
    'concepts/build_system/index.rst',
    'concepts/build_system/dts.rst',
    'concepts/conf.py',
    'concepts/concepts/archi_req.rst',
    'concepts/concepts/security.rst',
    'concepts/concepts/index.rst',
    'concepts/concepts/initial.rst',
    'concepts/concepts/uapi.rst',
    'concepts/index.rst',
    'concepts/sw_architecture/asp.rst',
    'concepts/sw_architecture/bsp.rst',
    'concepts/sw_architecture/syscalls.rst',
    'concepts/sw_architecture/index.rst',
)
concepts = custom_target('doc-concepts',
    input: concepts_rst,
    depend_files: [files('concepts/conf.py')],
    output: 'concepts',
    command: [sphinx, '-b', 'html', '-q', '-d',
        'build/doctrees',
        '-Dversion=' + meson.project_version(),
        join_paths(meson.current_source_dir(), 'concepts'),
        'doc/concepts',
    ])
doc_concepts = alias_target('doc-concepts', concepts)

concepts_pdf = custom_target('doc-concepts-pdf',
    input: concepts_rst,
    depend_files: [files('concepts/conf.py')],
    output: 'concepts_pdf',
    command: [sphinx, '-b', 'simplepdf', '-q',
        '-d', 'build/doctrees',
        '-Dversion=' + meson.project_version(),
        join_paths(meson.current_source_dir(), 'concepts'),
        'doc/concepts_pdf',
    ])
doc_concepts_pdf = alias_target('doc-concepts-pdf', concepts_pdf)

internals_rst = files(
    'internals/_static/figures/outpost.ico',
    'internals/_static/figures/outpost.png',
    'internals/conf.py',
    'internals/Doxyfile',
    'internals/index.rst',
)
internals = custom_target('doc-internals',
    input: internals_rst,
    depend_files: [files('internals/conf.py')],
    output: 'internals',
    command: [sphinx, '-b', 'html', '-q', '-d',
        'build/doctrees',
        '-Dversion=' + meson.project_version(),
        join_paths(meson.current_source_dir(), 'internals'),
        'doc/internals',
    ])
doc_internals = alias_target('doc-internals', internals)

doc = alias_target(
    'doc',
    concepts,
    internals,
)
