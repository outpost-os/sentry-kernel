
# very same header name, generated from corresponding svd
lpuart_h = custom_target('gen_lpuart',
    input: peripheral_defs_in,
    output: '@0@_defs.h'.format('lpuart'),
    depends: [ svd_json ],
    command: [
        jinja_cli, '-d', svd_json, '-o', '@OUTPUT@', '--define', 'NAME',
       'USART',
       '@INPUT@'
    ],
)
sentry_source_set.add(lpuart_h.to_list())

stm32_lpuart_dts_template_c = files(['stm32-lpuart-dt.c.in'])
stm32_lpuart_dts_template_h = files(['stm32-lpuart-dt.h.in'])

stm32_lpuart_dtsgen_c = dtsgen.process(stm32_lpuart_dts_template_c)
stm32_lpuart_dtsgen_h = dtsgen.process(stm32_lpuart_dts_template_h)


# driver source selection
sentry_source_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: files('stm32-lpuart.c'))

sentry_private_gen_source_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: [ stm32_lpuart_dtsgen_c, stm32_lpuart_dtsgen_h ])
sentry_private_gen_header_set.add(when: 'CONFIG_SOC_FAMILY_STM32', if_true: [ lpuart_h ])
