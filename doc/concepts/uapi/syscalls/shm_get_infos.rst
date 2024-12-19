sys_shm_get_infos
"""""""""""""""""
.. _uapi_shm_get_infos:

**API definition**

   .. code-block:: c
      :caption: C UAPI for shm_get_infos syscall

      enum Status __sys_shm_get_infos(shmh_t shm);

**Usage**

   In Sentry, as explained in :ref:`SHM model definition chapter <shm_principles>`, a shared memory
   holds credential for its owner and user task. It also hold some memory-related shm_get_infos
   such as base address and size.

   These information set is useful to get back in user-space without requiring any DTS forge at application level.

   These informations can be received through this syscall, by fulfilling the shm_infos_t structure
   declared by the UAPI in the SVC Exchange area. The `shm_infos_t` is defined in the
   UAPI `<types.h>` header in C or through the uapi.systypes Rust mod.

   .. code-block:: C
      :linenos:
      :caption: shm_infos_t structure definition

      /* SHM informations data structure */
      typedef struct shm_infos {
        shmh_t   handle;  /*< SHM handle */
        uint32_t label;   /*< SHM label */
        size_t   base;    /*< SHM base address */
        size_t   len;     /*< SHM length in bytes */
        uint32_t perms;   /*< SHM permissions (mask of SHMPermission) */
      } shm_infos_t;



   The only input required for this syscall is the SHM handle, as given by the
   `sys_get_shmhandle()` syscall.

   When a given SHM credentials set for the current job is updated, the `sys_shm_get_infos()`
   returns an up-to-date content synchronously.

   .. code-block:: C
      :linenos:
      :caption: sample bare usage of sys_shm_get_infos

      uint32_t my_shm_label=0xf00UL;
      taskh_t myself;
      shm_infos_t infos;
      if (__sys_get_task_handle(myself_label) != STATUS_OK) {
         // [...]
      }
      copy_from_kernel(&myself, sizeof(taskh_t));
      if (__sys_get_shm_handle(my_shm_label) != STATUS_OK) {
         // [...]
      }
      copy_from_kernel(&my_shm_handle, sizeof(shmh_t));

      if (__sys_shm_get_infos(my_shm_handle)) {
        // [...]
      }
      copy_from_kernel(&infos, sizeof(shm_infos_t));
      printf("SHM base address is %lx\n", infos.base);

**Required capability**

   None.

**Return values**

   * STATUS_INVALID if the SHM do not exist, target do not exist or is not owned or used by the calling task
   * STATUS_OK
