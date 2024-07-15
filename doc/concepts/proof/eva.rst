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

EVA results, when being analyzed with the RTE plugin, are useful to check that there is no step in the program execution
for which a given (set of) values violate the RTE Checks. RTE checks are automatically added as C code annotation when building the
Abstract Syntax Tree, while EVA delivers all potential values that may trigger these RTE check.

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


This model, that include both RTE and EVA, highly reduce the number of ACSL code to write. Moreover, as EVA and RTE are sound,
no annotation is forgotten.

EVA integration with Sentry kernel
""""""""""""""""""""""""""""""""""



EVA coverage
""""""""""""



Alarms and reports
""""""""""""""""""
