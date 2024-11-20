sys_dma_unassign_stream
"""""""""""""""""""""""
.. _uapi_dma_unassign_stream:

**API definition**

   .. code-block:: rust
      :caption: Rust UAPI for dma_unassign_stream syscall

      mod uapi {
         fn dma_unassign_stream(handle: dmah_t) -> Status
      }

   .. code-block:: c
      :caption: C UAPI for dma_unassign_stream syscall

      enum Status sys_dma_unassign_stream(dmah_t handle);

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

   A DMA stream may stop by itself when configured as a single copy DMA. In that case,
   the owning job only needs to wait for the `Transfer Complete` event. The suspend action
   is also allowed while the DMA transfer is not terminated. In such a configuration,
   if the `Transfer Complete` event is received, the DMA stream is automatically set as
   assigned (i.e. not started).

   A DMA stream can be assigned as soon as the target DMA channel is currently unassigned.
   A DMA stream can be unassigned as soon as the target DMA channel is suspended or assigned.
   A started (or resumed) DMA stream can't be unassigned.

.. note::
    When a single chunk DMA stream terminates (TC event received), the kernel consider the
    stream as `assigned`, and can be directly unassigned


**Example**

   .. code-block:: C
      :linenos:
      :caption: sample DMA stream unassignation

      if (sys_dma_start_stream(stream_handle) != STATUS_OK) {
         // the channel may be already assigned, unassign first
      }
      if (sys_wait_for_event(EVENT_TYPE_DMA, WFE_WAIT_FOREVER) != STATUS_OK) {
         // error while waiting for DMA event
      }
      // handle DMA event corresponding to previously started DMA stream

      // unasign stream if Transfer Complete event received
      if (sys_dma_unassigned_stream(stream_handle) != STATUS_OK) {
         // the channel may be already assigned, unassign first
      }

**Required capability**

   Like all other DMA-related syscalls, this syscall needs the calling task to hold the CAP_DEV_DMA capability.

**Return values**

   * STATUS_INVALID if the handle do not exist or the DMA stream is not currently assigned
   * STATUS_DENIED if the stream is not owned or the CAP_DEV_DMA is not hold by the task
   * STATUS_OK if the stream has been assigned

**See also**

    `sys_dma_assign_stream` (2), `sys_dma_unassign_stream` (2), `sys_dma_start_stream` (2), `sys_dma_suspend_stream` (2),
    `sys_get_dma_stream_handle` (2)
