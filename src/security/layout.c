// SPDX-FileCopyrightText: 2023 Ledger SAS
// SPDX-License-Identifier: Apache-2.0

/**
 * \file Memory-related security checks
 * TODO: handling pointer type (u8* vs u32* to detect borders
 * coverage properly through the target type len with sizeof & typeof)
 */
secure_bool_t pointer_targets_task_memory(size_t ptr, task_t task)
{
    return SECURE_FALSE;
}

secure_bool_t pointer_targets_task_code(size_t ptr, task_t task)
{
    return SECURE_FALSE;
}

secure_bool_t pointer_targets_task_stack(size_t ptr, task_t task)
{
    return SECURE_FALSE;
}

secure_bool_t pointer_targets_task_heap(size_t ptr, task_t task)
{
    return SECURE_FALSE;
}

secure_bool_t pointer_targets_task_device(size_t ptr, task_t task)
{
    return SECURE_FALSE;
}

