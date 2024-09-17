sys_shm_get_infos
"""""""""""""""""
.. _uapi_shm_get_infos:

**API definition**

   .. code-block:: rust
      :caption: Rust UAPI for shm_get_infos syscall

      mod uapi {
         fn shm_get_infos(shm: shm_t) -> Status
      }

   .. code-block:: c
      :caption: C UAPI for shm_get_infos syscall

      enum Status sys_shm_get_infos(shmh_t shm);

**Usage**

   In Sentry, as explained in :ref:`SHM model definition chapter <shm_principles>`, a shared memory
   hold credential for its owner and user task. It also hold some memory-related shm_get_infos
   such as base address and size.

   These informations are useful to get back un userspace without requiring any DTS forge at application level.

   These informations can be received through this syscall, by fullfilling the shm_infos_t structure
   declared by the UAPI in the SVC Exchange area. The `shm_infos_t` is defined in the
   UAPI `<types.h>` header in C or through the uapi.systypes Rust mod.

   .. code-block:: C
      :linenos:
      :caption: shm_infos_t structure definition

      /* Exchange event header for all events received in SVC Exchange area */
      typedef struct shm_infos {
        shmh_t   handle;  /*< SHM handle */
        uint32_t label;   /*< SHM label */
        size_t   base;    /*< SHM base address */
        size_t   len;     /*< SHM length in bytes */
        uint32_t perms;   /*< SHM permissions (mask of SHMPermission) */
      } shm_infos_t;



   The lonely input required for this syscall is the SHM handle, as given by the
   `sys_get_shmhandle()` syscall.

   When a given SHM credentials for the current job is upgraded, the `sys_shm_get_infos()`
   returns an uptodate content synchronously.

   .. code-block:: C
      :linenos:
      :caption: sample bare usage of sys_shm_get_infos

      uint32_t my_shm_label=0xf00UL;
      taskh_t myself;
      shm_infos_t infos;
      if (sys_get_task_handle(myself_label) != STATUS_OK) {
         // [...]
      }
      copy_to_user(&myself, sizeof(taskh_t));
      if (sys_get_shm_handle(my_shm_label) != STATUS_OK) {
         // [...]
      }
      copy_to_user(&my_shm_handle, sizeof(shmh_t));

      if (sys_shm_get_infos(my_shm_handle)) {
        // [...]
      }
      copy_to_user(&infos, sizeof(shm_infos_t));
      printf("SHM base address is %lx\n", infos.base);

**Required capability**

   None.

**Return values**

   * STATUS_INVALID if the SHM do not exist, target do not exist or is not owned or used by the calling task
   * STATUS_OK
