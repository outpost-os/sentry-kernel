Value analysis
---------------

.. _proof_eva:

.. index::
    single: EVA; integration

About EVA
"""""""""

EVA is the Value analysis plugin of Frama-C. This plugin allows to validate all the possibilities of
a given execution path considering a given entrypoint and a given set of inputs values.

Eva usage allows to cover to possible execution path, requiring to properly define all the input in a way that
specified input set is equal (bigger in the real life) to the effective possible inputs on the target.

This means that the analysis is based on a over-definition of the input set in order to cover all the possibilities
and ensure the correctness of the analysis results.

EVA results are generated in collaboration with RTE plugin. RTE checks are automatically added as C code annotation
when building the Abstract Syntax Tree, while EVA delivers all potential values that may trigger these RTE checks.

These results are useful to check that there is no step in the program execution for which a given (set of) values
violate the local RTE checks.


Here is a typical AST representation of a Sentry peace of code, with RTE annotations added:

.. code-block:: c
  :linenos:
  :caption: Auto-generated rte annotations

  /*@ assert rte: pointer_value: \object_pointer(shm_meta); */
  /*@ assert rte: mem_access: \valid_read(&shm_meta->baseaddr); */
  mpu_cfg.addr = shm_meta->baseaddr;
  /*@ assert rte: pointer_value: \object_pointer(shm_meta); */
  /*@ assert rte: mem_access: \valid_read(&shm_meta->size); */
  mpu_cfg.size = mpu_convert_size_to_region_21(shm_meta->size);
  status = mgr_mm_shm_is_writeable_by(shm,user,& result);
  if (status != (unsigned int)K_STATUS_OKAY) {
    tmp_2 = 1;
  }

EVA then delivers all the possible values of the locally acceded memory cells (here being ``shm_meta``, ``shm_meta->size``, etc.),
while RTE check that all assertions are valid.


This model, that includes both RTE and EVA, highly reduces the number of ACSL code to write. Moreover, as EVA and RTE are sound,
no annotation is forgotten.

EVA integration with Sentry kernel
""""""""""""""""""""""""""""""""""

As EVA requires an entrypoint in order to launch value analysis, EVA-related tests requires a dedicated ``main`` entry.
Each test directory in the Sentry kernel then hold two files:

   * the ``meson.build`` file related to the test declaration
   * a single C file that hold the effective entrypoint for EVA

A typical EVA entrypoint for Sentry hold the following:

.. code-block:: c
  :linenos:
  :caption: EVA entrypoint for kernel startup analysis

  void kernel_entrypoint(void)
  {
    /** INFO: inject garbage in metadata. This structure is build system forged.
     * This allows to:
     * 1. avoid uninitialized error from frama-C
     * 2. generate potential invalid inputs values from corrupted build system
     */
    Frama_C_task_init_meta();
    /* calling kernel entrypoint */
    _entrypoint();
  }

We can see here that the entrypoint first initialize kernel task metadata, then
directly execute the Sentry kernel entrypoint directly.

This is required as task metadata are not a part of the kernel ELF file build,
but is instead updated by the build system when applications are included to the system.

To ensure an over-definition of the possible inputs values for EVA, metadata content
is forged using Frama-C primitives, delivering complete randomness into all the metadata table
content. otherwise, a zero'ed table would be used, highly reducing the potential path traversals.

These metadata being the only external content that requires pre-initialization,
entrypoint path is fully covered by EVA plugin.

In order to generate clean randomness for metadata table, Frama-C specific fully random sources,
that generates complete coverage is accessible through the Frama-C framework:

.. code-block:: c
  :linenos:
  :caption: EVA entropy sources

  extern volatile int Frama_C_entropy_source_int __attribute__((unused))
  __attribute__((FRAMA_C_MODEL));
  extern volatile uint8_t Frama_C_entropy_source_u8 __attribute__((unused))
  __attribute__((FRAMA_C_MODEL));
  extern volatile uint16_t Frama_C_entropy_source_u16 __attribute__((unused))
  __attribute__((FRAMA_C_MODEL));
  extern volatile uint16_t Frama_C_entropy_source_u32 __attribute__((unused))
  __attribute__((FRAMA_C_MODEL));
  extern volatile uint8_t Frama_C_entropy_source_bool __attribute__((unused))
  __attribute__((FRAMA_C_MODEL));

These entropy sources can be used to generate randomness in any memory cell, so
that Frama-C will consider that such memory cell hold unpredictable value.

.. note::
    It is also possible to generate unpredictable, yet being a part of a reduced set
    if needed

EVA coverage
""""""""""""

EVA is able to define the coverage of all the accessible C instructions that could,
in theory, be reached through ``_entrypoint``. The coverage information, including
the C instruction coverage and sub-programs (C functions) coverage is accessible.

When post-analyzing generated session, the unreachable code is clearly visible. Such code can be:

   * dead code (checks that have been already made and can't be triggered considering the data flow)
   * unfeasible branches
   * defensive code (fault resilient)

As first cases can be fixed, the other part can't be considered at proof level, and should be explicitly
denoted as `defensive code`.

Alarms and reports
""""""""""""""""""

Alarm analysis is required and generates false positives (EVA being sound, no false-negative exist but false  positives alarms may
be generated). Reducing false positive is done with ACSL helpers, such as ``assert`` marker, in order to help with
local post-checked value. In some cases, it may (for complex sub-programs) be required to define more complete contracts.

The less border effect and complexity sub-program have, the less false positives are generated.

Th main false positive that is encounter in a kernel implementation is the forge and access to the user-space task memory, as
this memory is not a part of the kernel itself. On the other hand, it is though possible to declare application memory as
external writeable memory, in the very same way devices are declared to Frama-C. Separated proofs allow such mechanism
as libraries responsible for interacting with user-space content and libraries responsible for interacting with devices are
not the same, so that only a single external content can be declared to Frama-C for each analysis.
