# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

stream_template_c = files(['dma-dt.c.in'])
stream_dtsgen_c = dtsgen.process(stream_template_c)

# TODO: create manager_private_gen_source_set
managers_private_gen_header_set.add(stream_dtsgen_c)
