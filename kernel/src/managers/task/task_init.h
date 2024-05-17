// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#ifndef TASK_INIT_H
#define TASK_INIT_H

#include <inttypes.h>
#include <sentry/thread.h>
#include <sentry/managers/task.h>

/*@
  @ assigns \nothing;
  */
uint32_t mgr_task_get_num(void);

void mgr_task_set_userspace_spawned(void);

#endif/*!TASK_INIT_H*/
