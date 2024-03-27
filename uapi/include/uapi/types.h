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


#ifndef __SENTRY_UAPI_TYPES_H
#define __SENTRY_UAPI_TYPES_H

#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

typedef enum {
  CPU_SLEEP_WAIT_FOR_INTERRUPT,
  CPU_SLEEP_WAIT_FOR_EVENT,
  CPU_SLEEP_FORBID_SLEEP,
  CPU_SLEEP_ALLOW_SLEEP,
} CPUSleep;

typedef enum EventType {
  EVENT_TYPE_NONE = 0,
  EVENT_TYPE_IPC = 1,
  EVENT_TYPE_SIGNAL = 2,
  EVENT_TYPE_IRQ = 4,
  EVENT_TYPE_ALL = 7,
} EventType;

typedef enum Precision {
  PRECISION_CYCLE,
  PRECISION_NANOSECONDS,
  PRECISION_MICROSECONDS,
  PRECISION_MILLISECONDS,
} Precision;

/**
 * List of Sentry resource types
 *
 * Multiple opaque are used in userspace. This opaques are namespaced and
 * manipulated at kernel level to ensure unicity, identification, etc.
 */
typedef enum ResourceType {
  RESOURCE_TYPE_PID = 1,
  RESOURCE_TYPE_DEVICE = 2,
  RESOURCE_TYPE_SHM = 4,
  RESOURCE_TYPE_DMA = 8,
} ResourceType;

typedef enum SHMPermission {
  /**
   * allows target process to map the SHM. No read nor write though
   */
  SHM_PERMISSION_MAP,
  /**
   * allows target process to read the mapped SHM. Requires MAP
   */
  SHM_PERMISSION_READ,
  /**
   * allows target process to write shared memory. Requires MAP
   */
  SHM_PERMISSION_WRITE,
  /**
   * allows target process to transfer SHM to another, pre-allowed, process
   */
  SHM_PERMISSION_TRANSFER,
} SHMPermission;

/**
 * Events tasks can listen on
 */
typedef enum Signal {
  /**
   * Abort signal
   */
  SIGNAL_ABORT = 1,
  /**
   * Timer (from alarm)
   */
  SIGNAL_ALARM,
  /**
   * Bus error (bad memory access, memory required)
   */
  SIGNAL_BUS,
  /**
   * Continue if previously stopped
   */
  SIGNAL_CONT,
  /**
   * Illegal instruction. Can be also used for upper provtocols
   */
  SIGNAL_ILL,
  /**
   * I/O now ready
   */
  SIGNAL_IO,
  /**
   * Broken pipe
   */
  SIGNAL_PIPE,
  /**
   * Event pollable
   */
  SIGNAL_POLL,
  /**
   * Termination signal
   */
  SIGNAL_TERM,
  /**
   * Trace/bp signal (debug usage only)
   */
  SIGNAL_TRAP,
  /**
   * 1st user-defined signal
   */
  SIGNAL_USR1,
  /**
   * 2nd user-defined signal
   */
  SIGNAL_USR2,

#ifdef CONFIG_BUILD_TARGET_AUTOTEST
  SIGNAL_PANIC_USER_HARD_FAULT,
  SIGNAL_PANIC_KERNEL_HARD_FAULT,
  SIGNAL_PANIC_USER_BUS_FAULT,
  SIGNAL_PANIC_KERNEL_BUS_FAULT,
  SIGNAL_PANIC_USER_USAGE_FAULT,
  SIGNAL_PANIC_KERNEL_USAGE_FAULT,
  SIGNAL_PANIC_USER_MEM_ACCESS,
  SIGNAL_PANIC_KERNEL_MEM_ACCESS,
  SIGNAL_PANIC_KERNEL_INVALID_USESPACE_INPUT,
  SIGNAL_PANIC_KERNEL_SHORTER_K_BUFFERS_CONFIG,
  SIGNAL_PANIC_KERNEL_INVALID_MANAGER_STATE,
  SIGNAL_PANIC_KERNEL_INVALID_MANAGER_RESPONSE,
  SIGNAL_PANIC_KERNEL_TIMEOUT,
  SIGNAL_PANIC_KERNEL_BAD_CFI_CALCULATION,
  SIGNAL_PANIC_HARDWARE_INVALID_STATE,
  SIGNAL_PANIC_HARDWARE_UNEXPECTED_MODIFICATION,
  SIGNAL_AUTOTEST_DONE,
  SIGNAL_AUTOTEST_FAILED,
  SIGNAL_AUTOTEST_TIMED_OUT,
#endif // CONFIG_BUILD_TARGET_AUTOTEST

} Signal;

typedef enum SleepMode {
  SLEEP_MODE_SHALLOW,
  SLEEP_MODE_DEEP,
} SleepMode;

typedef enum AlarmFlag {
  O_ALRM_START,
  O_ALRM_START_PERIODIC,
  O_ALRM_STOP,
} AlarmFlag;

/**
 * Sentry syscall return values
 * NonSense must never be returned, as it means that an
 * asynchronously updated return value.... has not been updated at all
 * This must raise a security exception. All syscalls that can't set
 * they return code synchronously (e.g. IPC), MUST use this value as
 * default one
 */
typedef enum Status {
  STATUS_OK,
  STATUS_INVALID,
  STATUS_DENIED,
  STATUS_NO_ENTITY,
  STATUS_BUSY,
  STATUS_ALREADY_MAPPED,
  STATUS_TIME_OUT,
  STATUS_CRITICAL,
  STATUS_TIMEOUT,
  STATUS_NON_SENSE,
} Status;

typedef enum Syscall {
  SYSCALL_EXIT,
  SYSCALL_GET_PROCESS_HANDLE,
  SYSCALL_GET_DEVICE_HANDLE,
  SYSCALL_YIELD,
  SYSCALL_SLEEP,
  SYSCALL_START,
  SYSCALL_MAP_DEV,
  SYSCALL_MAP_SHM,
  SYSCALL_UNMAP_DEV,
  SYSCALL_UNMAP_SHM,
  SYSCALL_SHM_SET_CREDENTIAL,
  SYSCALL_SEND_IPC,
  SYSCALL_SEND_SIGNAL,
  SYSCALL_WAIT_FOR_EVENT,
  SYSCALL_PM_MANAGE,
  SYSCALL_PM_SET_CLOCK,
  SYSCALL_LOG,
  SYSCALL_ALARM,
  SYSCALL_GET_RANDOM,
  SYSCALL_GET_CYCLE,
  SYSCALL_GPIO_GET,
  SYSCALL_GPIO_SET,
  SYSCALL_GPIO_RESET,
  SYSCALL_GPIO_TOGGLE,
  SYSCALL_GPIO_CONFIGURE,
  SYSCALL_IRQ_ACKNOWLEDGE,
} Syscall;

/**
 * A process label is a development-time fixed identifier that can be used hardcoded
 *  in the source code. This can be used in order to get back remote process effective
 * identifier from label at any time in order to communicate
 */
typedef uint32_t ProcessLabel;

typedef uint32_t ProcessID;

typedef enum SleepDuration_Tag {
  SLEEP_DURATION_D1MS,
  SLEEP_DURATION_D2MS,
  SLEEP_DURATION_D5MS,
  SLEEP_DURATION_D10MS,
  SLEEP_DURATION_D20MS,
  SLEEP_DURATION_D50MS,
  SLEEP_DURATION_ARBITRARY_MS,
} SleepDuration_Tag;

typedef struct SleepDuration {
  SleepDuration_Tag tag;
  union {
    struct {
      uint32_t arbitrary_ms;
    };
  };
} SleepDuration;

/* Exchange event header for all events received in SVC Exchange area */
typedef struct exchange_event {
    uint8_t type;   /*< event type, as defined in uapi/types.h */
    uint8_t length; /*< event data length, depending on event */
    uint16_t magic; /*< event TLV magic, specific to input event reception */
    uint8_t data[]; /*< event data, varies depending on length field */
} exchange_event_t;


#endif /* __SENTRY_UAPI_TYPES_H */
