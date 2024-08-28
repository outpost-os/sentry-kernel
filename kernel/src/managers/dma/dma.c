// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

kstatus_t mgr_dma_init(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}

kstatus_t mgr_dma_watchdog(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}

kstatus_t mgr_dma_get_owner(dmah_t d, taskh_t *owner)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_dma_autotest(void)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
#endif

kstatus_t mgr_device_get_dmah_from_interrupt(uint16_t IRQn, dmah_t *dmah)
{
    kstatus_t status = K_STATUS_OKAY;
    return status;
}
