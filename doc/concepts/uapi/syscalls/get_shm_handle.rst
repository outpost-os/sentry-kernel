sys_get_shm_handle
""""""""""""""""""
.. _uapi_shm_handle:

**API definition**

   .. code-block:: c
      :caption: C UAPI for get_shm_handle syscall

      enum Status __sys_get_shm_handle(uint32_t label);

**Usage**

   In Sentry, as explained in :ref:`SHM model definition chapter <shm_principles>`, a shared memory
   is unikely identified by its label, in the same way as tasks. the shared memory handle is forged
   at boot time so that its value can't be predefined at compile time. As a consequence,
   shared memory owner needs to ask for the SHM handle that correspond to a known labbel.

   When the shared memory is shared with another task by the SHM owner, both tasks (owner and user)
   can ask for the handle that correspond to the label. This allows two sharing model:

      * the owner task voluntary share the label with the user task (using IPC for example)
      * owner and user task share the label since compile time, using config-based or hard-coded label

   This syscall returns the handle corresponding to the label declared in the device-tree. this handle until
   the next reboot.

   .. code-block:: C
      :linenos:
      :caption: sample bare usage of sys_get_shm_handle

      uint32_t my_peer_label=0xbabe;
      taskh_t my_peer_handle;
      if (__sys_get_shm_handle(my_shm_label) != STATUS_OK) {
         // [...]
      }
      copy_from_kernel(&my_peer_handle, sizeof(shmh_t));

**Required capability**

   None.

**Return values**

   * STATUS_INVALID if the SHM do not exist or is not owned or used by the calling task
   * STATUS_OK
