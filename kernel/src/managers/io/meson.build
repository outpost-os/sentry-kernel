# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

# IO generic layer, over BSP (GPIO, EXTI...)

manager_io_template_c = files('io.c.in')

manager_io_c = dtsgen.process(manager_io_template_c)

managers_source_set.add(
    manager_io_c,
)
