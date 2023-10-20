// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * @file generic upper layer API for Sentry schedulers
 */

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
kstatus_t schedule(taskh_t t);

/**
 * @brief return the next eligible process dientified by its task handle
 *
 * The scheduler returns the next eligible process based on its current task set
 * and scheduling policy. The returned handle can be a real process or the idle
 * task, if no more user process is eligible.
 *
 * @return the next eligible task, identified by its handle
 */
taskh_t elect(void);
