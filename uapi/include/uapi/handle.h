// SPDX-FileCopyrightText: 2023-2024 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


#ifndef __SENTRY_UAPI_HANDLE_H
#define __SENTRY_UAPI_HANDLE_H

#ifndef __cpluplus
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

typedef uint32_t devh_t;
typedef uint32_t taskh_t;
typedef uint32_t shmh_t;
typedef uint32_t dmah_t;
#else
/*
 * Use C++ types definition while compiled in C++
 */
#include <cstdint>
using devh_t = uint32_t;
using taskh_t = uint32_t;
using shmh_t = uint32_t;
using dmah_t = uint32_t;
#endif /* __cpluplus */

#endif /* __SENTRY_UAPI_HANDLE_H */
