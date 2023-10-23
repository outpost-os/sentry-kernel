// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @def no task label definition
 *
 * At early bootup, before any task is started (even idle), the scheduler returns
 * a specially forged task label denoted 'babe'. This label is forbidden to user
 * tasks and used to detect 'no task exists at all, still in MSP bootup'
 */
#define SCHED_NO_TASK_LABEL   0xbabeUL

/**
 * @def idle task label definition
 *
 * When no task of the user task set is schedulable, the idle task is the lonely
 * task eligible. This special task is a dedicated thread that wfi() and yield()
 * so that the core can enter SLEEP mode while no interrupt rise and all tasks
 * are blocked (external event wait, sleep, etc.).
 * The idle task has a dedicated label denoted 'cafe'. This label is forbidden
 * to user tasks.
 */
#define SCHED_IDLE_TASK_LABEL 0xcafeUL

/**
 * @file generic upper layer API for Sentry schedulers
 */

kstatus_t sched_fifo_init(void);

/**
 * @brief Add a task to the scheduler queue
 *
 * The task handle associated to a given process is now schedulable and
 * need to be executed. The scheduler take it and add it to its current task
 * set and will schedule it based on its current policy and current task set
 * state.
 * This function is typically called at spawn time, when starting the operating
 * system and adding all boot-time schedulable tasks.
 *
 * @param t[in]: task handle to schedule
 *
 * @return should return K_STATUS_OKAY. Otherwise this is a security violation,
 *  as the scheduler table is configured based on the system max number of tasks
 *  defined at compile time.
 */
kstatus_t sched_schedule(taskh_t t);

/**
 * @brief return the next eligible process dientified by its task handle
 *
 * The scheduler returns the next eligible process based on its current task set
 * and scheduling policy. The returned handle can be a real process or the idle
 * task, if no more user process is eligible.
 *
 * @return the next eligible task, identified by its handle
 */
taskh_t sched_elect(void);

/**
 * @brief return the currently being executed task
 *
 * This helper function is used in order to get back the currently
 * being executed task when having only the stack pointer as reference
 * (typically in handlers). This allows easier task manipulation and
 * context saving in the task switching module.
 * The scheduler do not handle the context switching but only delivers
 * the policy to get the next task to execute or the currently executed task.
 *
 * The idle task taskh_t is { 0, 0xcafe, HANDLE_TASKID}
 *
 * @return the next task handle reference to execute. Can be idle task
 */
taskh_t sched_get_current(void);
