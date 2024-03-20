# UAPI header generation is always required

pkg_config = import('pkgconfig')
uapi_rust_std = 'rust_std=2021'
uapi_rust_libfile = files('uapi/lib.rs')

subdir('include/uapi')
subdir('uapi')

if with_uapi_opt

py3 = pymod.find_installation('python3', modules: ['git'])

# XXX:
#  This deps is designed for userspace (libshied) only
#  As in linux kernel, uapi headers are not used w/ a kernel name and/or uapi
#  prefix. So, add the uapi include subdir in "include_directories".
sentry_c_uapi_dep = declare_dependency(
    link_with: uapi_rs_lib,
    sources: [ uapi_h ],
    compile_args: [ global_build_args, target_arch_args ],
    include_directories: [ userspace_uapi_include_dir ],
)

pkg_config.generate(
    uapi_rs_lib,
    filebase: 'uapi',
    extra_cflags: [ global_build_args, target_arch_args ],
)

install_data(
  'task.Kconfig',
  install_dir : get_option('datadir') / 'configs',
)

install_subdir(
  'uapi',
  install_dir: get_option('datadir') / 'cargo/repository/sentry-uapi',
  strip_directory: true,
  install_tag: 'devel',
)

vendoring_py_wrapper = '''
import git

repo = git.Repo(search_parent_directories=True)
print('{');
print('  "git": {')
print('    "sha1": "{}"'.format(repo.head.commit.tree.hexsha))
print('}');
'''

gen_cargo_hash = custom_target(
  'forge_cargo_hashfile',
  output: '.cargo_vcs_info.json',
  command: [ py3, '-c', vendoring_py_wrapper ],
  capture: true,
  install: true,
  install_dir: get_option('datadir') / 'cargo/repository/sentry-uapi',
  install_tag: 'devel',
  build_always: true,
)

install_data(
  'task.Kconfig',
  install_dir : get_option('datadir') / 'configs',
)

install_data(
  '.cargo-checksum.json',
  install_dir: get_option('datadir') / 'cargo/repository/sentry-uapi',
)

endif #with_uapi
