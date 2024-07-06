#ifndef MEMORY_PRIVATE_H
#define MEMORY_PRIVATE_H

#include <sentry/ktypes.h>

kstatus_t mgr_mm_shm_init(void);

kstatus_t mgr_mm_map_kernel_txt(void);

kstatus_t mgr_mm_map_kernel_data(void);

secure_bool_t mgr_mm_configured(void);

#endif/*!MEMORY_PRIVATE_H*/
