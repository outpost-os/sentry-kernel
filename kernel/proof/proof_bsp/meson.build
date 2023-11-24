subdir('proof_exti')
subdir('proof_pwr')
subdir('proof_rcc')
# depending on the target SoC, RNG device may not exist
if kconfig_data.get('CONFIG_HAS_RNG', 0) == 1
subdir('proof_rng')
endif
