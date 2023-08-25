project('sentry-kernel', 'c',
    meson_version: '>=1.1.0',
    version: run_command('dunamai', 'from', 'git', '--style', 'semver', '--dirty', check: true).stdout().strip(),
    default_options: ['c_std=gnu11', 'default_library=static', 'warning_level=3' ],
    license: 'Apache-2.0',
    license_files: [ 'LICENSE' ],
)

top_dir = meson.current_source_dir()

# dunamai is used for version sync with gconf (in the same way poetry-dynamic-versioning does)
pymod = import('python')
py3 = pymod.find_installation('python3', modules: ['dunamai'])


# kernel code shared include directory
kernel_inc = include_directories('include/sentry')

# userspace exported include directory
uapi_inc = include_directories('include/uapi')

# all sources are there
subdir('src');

# auto-generation (jinja2, json) tooling is there
subdir('tools');
