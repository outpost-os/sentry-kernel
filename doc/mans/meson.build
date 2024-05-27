# SPDX-FileCopyrightText: 2023-2024 Ledger SAS
# SPDX-License-Identifier: LicenseRef-LEDGER

mandb = []

foreach syscall_file: syscalls_src
target_name = 'man_gen_syscall_' + fs.name(syscall_file)

mandb += custom_target(
  target_name,
  input: syscall_file,
  output: 'sys_@BASENAME@.2',
  command: [
     pandoc,
     '-f', 'rst',
     '-t', 'man',
     '-s',
     '-V', 'header=Sentry programmer\'s manual',
     '-V', 'section=2',
     '-o', '@OUTPUT@',
     '@INPUT@',
  ],
  install_tag: 'man',
  install : true,
  install_dir : join_paths(get_option('mandir'), 'man2')
)
endforeach

# man pages build can be trigger by mandb target
man_tgt = alias_target('mandb', mandb)
