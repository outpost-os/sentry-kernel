sys_exit
""""""""

**API definition**

   .. code-block:: rust
      :caption: Rust UAPI for exit syscall

      mod uapi {
         fn exit(status: u32) -> Status
      }

   .. code-block:: c
      :caption: C UAPI for exit syscall

      enum Status sys_exit(uint32_t status);


**Usage**

   Terminate the current job with status code given in argument.
   Any non-zero status code is considered as an abnormal status code and is
   passed to job termination mechanism.

**Required capability**

   None.

**Return values**

   End the current job, never returns.

   The exit status is used by the `exitpoint` symbol as only argument. This symbol is
   typically the `_exit` symbol of the libc that can execute post-execution triggers.

   If the libc supports it, the application developer can define such a trigger so
   that it can be called by the `_exit` function in a post exit context in order to
   properly clean the task data. See the libShield documentation for more information.

   See :ref:`job termination chapter <job_termination>` for more informations.

   .. note::
       The goal here is to support runtime-based termination call with potential
       application developper hooks, so that a unified central handler
       can react to various status code values, wherever the `exit()` call is made in the
       job implementation
