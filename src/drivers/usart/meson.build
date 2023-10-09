
if kconfig_data.get('CONFIG_BUILD_TARGET_DEBUG', 0) == 1

# very same header name, generated from corresponding svd
usart_h = custom_target('gen_usart',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('usart'),
    depends: [ svd_json ],
    command: [
        jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME',
       'USART',
       '@INPUT@'
    ],
)
sentry_source_set.add(usart_h.to_list())

# driver source selection
sentry_source_set.add(when: 'CONFIG_BUILD_TARGET_DEBUG', if_true: files('stm32-usart.c'))

endif
