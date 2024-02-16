// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef HANDLE_H
#define HANDLE_H

#include <uapi/handle_defs.h>
#include <uapi/handle.h>

/**
 * @file Sentry handles specification.
 *
 * All handles are dynamically forged, mostly from DTS files, and handle opaques
 * are uint32_t values with subsets.
 * Handles are unique on the system.
 *
 * All handle-associated objects are stored in generated tables, based on
 * the project dtsi files parsing.
 * these tables are under the responsavility of each object manager
 * (e.g. task manager, device manager, etc.) and manipulating each element
 * identified by the handle is done through the manager kernel-wide API.
 *
 * @info: such model ensure that each manager table storage is local to the manager.
 *  This make the storage structure, field evolution, etc. opaque to all others
 *  kernel modules. Moreover, this allows to avoid any kernel pointer usage.
 *
 * @info: as some actions may require high reactivity, table lookup should be
 * avoided if not needed. To do so, each handle store some usefull informations
 * that can be directly used by the target service, until the handle existance
 * (integrity check) is made. For e.g. setting a GPIO pin do not need to get back
 * the io manager information using the ioh_t argument, as the gpio port and
 * pin is already hardcoded in the ioh_t specific part of the handler.
 */

#define HANDLE_ID_SHIFT         13UL
#define HANDLE_ID_MASK          0x7fff8000UL

#define HANDLE_FAMILY_SHIFT    29UL
#define HANDLE_FAMILY_MASK     0xe0000000UL

static inline uint32_t handle_convert_shmh_to_u32(shmh_t h) {
    return (uint32_t)(((h.id << HANDLE_ID_SHIFT) & HANDLE_ID_MASK) |
               ((h.family << HANDLE_FAMILY_SHIFT) & HANDLE_FAMILY_MASK) |
               (h.reserved & 0xfff1UL));
}

static inline uint32_t handle_convert_dmah_to_u32(dmah_t h) {
    return (uint32_t)(((h.id << HANDLE_ID_SHIFT) & HANDLE_ID_MASK) |
               ((h.family << HANDLE_FAMILY_SHIFT) & HANDLE_FAMILY_MASK));
}


#define handle_convert_to_u32(T) _Generic((T),  \
              shmh_t:  handle_convert_shmh_to_u32,   \
              dmah_t:  handle_convert_dmah_to_u32,   \
        ) (T)

#endif/*!HANDLE_DEFS_H*/
