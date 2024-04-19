// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef SENTRY_MANAGERS_DEVICE_H
#define SENTRY_MANAGERS_DEVICE_H

#include <inttypes.h>
#include <uapi/device.h>
#include <uapi/handle.h>
#include <sentry/ktypes.h>

kstatus_t mgr_device_init(void);

kstatus_t mgr_device_watchdog(void);

secure_bool_t mgr_device_exists(devh_t d);

kstatus_t mgr_device_get_info(devh_t, const devinfo_t **devinfo);

uint32_t mgr_device_get_capa(devh_t d);

kstatus_t mgr_device_get_owner(devh_t d, taskh_t *owner);

kstatus_t mgr_device_get_devhandle(uint32_t dev_label, devh_t *devhandle);

kstatus_t mgr_device_set_map_state(devh_t d, secure_bool_t mapped);

kstatus_t mgr_device_get_map_state(devh_t d, secure_bool_t *mapped);

kstatus_t mgr_device_get_configured_state(devh_t d, secure_bool_t *configured);

kstatus_t mgr_device_configure(devh_t dev);

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
kstatus_t mgr_device_autotest(void);
#endif

kstatus_t mgr_device_get_devh_from_interrupt(uint16_t IRQn, devh_t *devh);

/**
 * Iterate over the device list, starting with id==id.
 * Return the devinfo of the current id increment, or set devinfo to NULL and return K_ERROR_NOENT if
 * the dev list walk is terminated
 */
kstatus_t mgr_device_walk(const devinfo_t **devinfo, uint8_t id);


kstatus_t mgr_device_get_devinfo_from_interrupt(uint16_t IRQn, const devinfo_t **devinfo);

kstatus_t mgr_device_get_clock_config(const devh_t d, uint32_t *clk_id, uint32_t *bus_id);

#endif/*SENTRY_MANAGERS_DEVICE_H*/
