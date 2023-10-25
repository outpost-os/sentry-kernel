
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

stm32_usart_dts_template_c = files(['stm32-usart-dt.c.in'])
stm32_usart_dts_template_h = files(['stm32-usart-dt.h.in'])

stm32_usart_dtsgen_c = dtsgen.process(stm32_usart_dts_template_c)
stm32_usart_dtsgen_h = dtsgen.process(stm32_usart_dts_template_h)


# driver source selection
sentry_source_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: files('stm32-usart.c'))

sentry_private_gen_source_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: [ stm32_usart_dtsgen_c, stm32_usart_dtsgen_h ])
sentry_private_gen_header_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: [ usart_h ])

endif
