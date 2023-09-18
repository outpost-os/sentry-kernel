svd_json = meson_svd_proj.get_variable('svd_json')
jinja_cli = meson_svd_proj.get_variable('jinja_cli')
irq_defs_in = meson_svd_proj.get_variable('irq_defs_in')
layout_in = meson_svd_proj.get_variable('layout_in')

irq_def_h = custom_target('gen_irq_defs',
   input: irq_defs_in,
    output: '@BASENAME@',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '@INPUT@' ],
)

layout_h = custom_target('gen_layout',
    input: layout_in,
    output: '@BASENAME@',
    depends: [ svd_json ],
    command: [ jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '@INPUT@' ],
)
