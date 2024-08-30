# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-License-Identifier: Apache-2.0

dma_sources = files(
    'dma.c',
)

stream_template_c = files(['dma-dt.c.in'])
stream_dtsgen_c = dtsgen.process(stream_template_c)

stream_template_h = files(['dma-dt.h.in'])
stream_dtsgen_h = dtsgen.process(stream_template_h)

# TODO: create manager_private_gen_source_set
managers_private_gen_header_set.add(stream_dtsgen_c)
managers_private_gen_header_set.add(stream_dtsgen_h)

managers_source_set.add(dma_sources)
