sys_dma_assign_stream
"""""""""""""""""""""
.. _uapi_dma_assign_stream:

**API definition**

   .. code-block:: c
      :caption: C UAPI for dma_assign_stream syscall

      enum Status __sys_dma_assign_stream(dmah_t handle);

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

   A DMA stream can be assigned as soon as the target DMA channel is currently unassigned.
   The DMA stream assignation consists in configuring the DMA channel with all the DMA streams
   attributes values. Assigning a stream do not start it.

   A started DMA stream may stop by itself when configured as a single copy DMA. In that case,
   the owning job only needs to wait for the `Transfer Complete` event. The suspend action
   is also allowed while the DMA transfer is not terminated. In such a configuration,
   if the `Transfer Complete` event is received, the DMA stream is automatically set as
   assigned (i.e. not started).




**Example**

   .. code-block:: C
      :linenos:
      :caption: sample DMA stream assignation

      if (__sys_dma_assign_stream(stream_handle) != STATUS_OK) {
         // the channel may be already assigned, unassign first
      }

**Required capability**

   Like all other DMA-related syscalls, this syscall needs the calling task to hold the CAP_DEV_DMA capability.

**Return values**

   * STATUS_INVALID if the handle do not exist or the target DMA channel is busy (not unassigned)
   * STATUS_DENIED if the stream is not owned or the CAP_DEV_DMA is not hold by the task
   * STATUS_OK if the stream has been assigned

**See also**

    `sys_dma_assign_stream` (2), `sys_dma_unassign_stream` (2), `sys_dma_start_stream` (2), `sys_dma_suspend_stream` (2),
    `sys_get_dma_stream_handle` (2)
