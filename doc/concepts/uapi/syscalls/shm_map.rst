sys_map_shm
"""""""""""

**API definition**

   .. code-block:: c
      :caption: C UAPI for device mapping syscall

      enum Status __sys_map_shm(shmh_t shm);
      enum Status __sys_unmap_shm(shmh_t shm);

**Usage**

   Map a given shared memory into the task context.

   Once returning from this syscall, the shared-memory is mapped at its corresponding
   address as declared in its device tree node.

   .. code-block:: C
      :linenos:
      :caption: sample bare usage of sys_map_shm

      enum Status res = STATUS_INVALID;
      shmh_t shm;
      uint32_t shm_label = 0xf00UL;

      if (__sys_get_shmhandle(shm_label) != STATUS_OK) {
         // [...]
      }
      res = __sys_map_shm(shm_label);

   .. note::
      the SHM credential must be set through `sys_shm_set_credential()` in order to be allowed to map the SHM.

    Unmapping a shared memory is made using `sys_shm_unmap()`, in the very same way SHM is mapped.
    Unmapping the shared memory free the associated memory ressource of the task immediately.

**Required capability**

   None.

**Return values**

   For `sys_shm_map()`:

      * STATUS_INVALID if the SHM handle do not exist or is not associated at all to the calling task
      * STATUS_DENIED if the SHM credential do not allow mapping
      * STATUS_ALREADY_MAPPED if SHM is already mapped
      * STATUS_OK

   For `sys_shm_unmap()`:

      * STATUS_INVALID if the SHM handle do not exist or is not mapped
      * STATUS_OK
