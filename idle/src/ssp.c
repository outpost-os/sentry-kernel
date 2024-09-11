// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

#include <uapi.h>

void __stack_chk_fail(void)
{
    sys_exit(STATUS_CRITICAL);
    while (1) {
    };
}
