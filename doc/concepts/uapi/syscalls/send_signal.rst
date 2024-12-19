sys_send_signal
"""""""""""""""

**API definition**

   .. code-block:: c
      :caption: C UAPI for send_signal syscall

      enum Status __sys_send_signal(taskh_t target, enum Signal signal);

**Usage**

   Emit a signal to the target identified by the `target` opaque, as received by the
   `sys_get_process_handle()` syscall.

   If the target exists and is running, the signal is added to its input signal queue.
   The syscall is a non-blocking, synchronous syscall and do not generate any
   scheduling impact.
   The signal management is an asynchronous communication mechanism, meaning that
   the syscall returns **before** that the target do actually receive the signal.

   .. warning::
      Only one signal at a time is supported by a peer for a given source. If a source
      send a new signal to a peer that did not already received the previous one, the
      send_signal syscall will return a STATUS_BUSY flag

   The Sentry supported list of signals are defined in :ref:`UAPI model definition <signals>`.

   .. code-block:: C
      :linenos:
      :caption: sample bare usage of sys_send_signal

      uint32_t seed = 0;
      if (__sys_send_signal(target, SIGNAL_USR1) != STATUS_OK) {
         // [...]
      }

   .. note::
       If a previously working signal request starts to fail with an invalid return, this
       is typically the consequence of a target respawn or termination

   .. note::
       See :ref:`get_task_handle() <uapi_task_handle>` UAPI specification to learn about how to forge the target
       variable value

**Required capability**

   None.

**Return values**

   * STATUS_BUSY if the target has its input signal queue full
   * STATUS_INVALID if the target do not exist in the current job domain
   * STATUS_OK
