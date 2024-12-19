sys_dma_start_stream
""""""""""""""""""""
.. _uapi_dma_start_stream:

**API definition**

   .. code-block:: c
      :caption: C UAPI for dma_start_stream syscall

      enum Status __sys_dma_start_stream(dmah_t handle);

**Usage**

   A task can manipulate multiple DMA streams, and is allowed to support multiple stream
   configurations that may use the very same hardware DMA channel.

   DMA streams lifecycle is designed so that DMA streams can be easily assigned, started,
   suspended, resumed, and unassigned during the job lifecycle, depending on its own need.

   DMA stream lifecycle must respect the following state automaton:

   1. assign a DMA stream to the corresponding DMA channel
   2. start the previously assigned DMA stream
   3. if needed:

      1. suspend the DMA stream
      2. resume the DMA stream

   4. unassign the DMA stream

   Once assigned, a DMA stream needs to be voluntary started by the owning job.
   Starting a DMA is a synchronous syscall. The DMA streams start immediately. The
   calling job can then directly wait for DMA event as soon as the start syscall
   has returned without error.

   A DMA stream may stop by itself when configured as a single copy DMA. In that case,
   the owning job only needs to wait for the `Transfer Complete` event. The suspend action
   is also allowed while the DMA transfer is not terminated. In such a configuration,
   if the `Transfer Complete` event is received, the DMA stream is automatically set as
   assigned (i.e. not started).


.. note::
    There is no such `stop_stream` action. For a given started DMA stream, stopping
    a DMA stream is done using the `sys_dma_suspend_stream()+sys_dma_unassign_stream()` couple

**Example**

   .. code-block:: C
      :linenos:
      :caption: sample DMA stream start sequence

      #include <uapi.h>

      if (__sys_dma_start_stream(stream_handle) != STATUS_OK) {
         // the channel may be already assigned, unassign first
      }
      if (__sys_wait_for_event(EVENT_TYPE_DMA, WFE_WAIT_FOREVER) != STATUS_OK) {
         // error while waiting for DMA event
      }
      // handle DMA event corresponding to previously started DMA stream
      // [...]

**Required capability**

   Like all other DMA-related syscalls, this syscall needs the calling task to hold the CAP_DEV_DMA capability.

**Return values**

   * STATUS_INVALID if the handle do not exist or the DMA stream is not currently assigned
   * STATUS_DENIED if the stream is not owned or the CAP_DEV_DMA is not hold by the task
   * STATUS_OK if the stream has been started

**See also**

    `sys_dma_assign_stream` (2), `sys_dma_unassign_stream` (2), `sys_dma_start_stream` (2), `sys_dma_suspend_stream` (2),
    `sys_get_dma_stream_handle` (2)
