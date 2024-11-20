sys_dma_suspend_stream
""""""""""""""""""""""
.. _uapi_dma_start_stream:

**API definition**

   .. code-block:: rust
      :caption: Rust UAPI for dma_suspend_stream syscall

      mod uapi {
         fn dma_suspend_stream(handle: dmah_t) -> Status
      }

   .. code-block:: c
      :caption: C UAPI for dma_suspend_stream syscall

      enum Status sys_dma_suspend_stream(dmah_t handle);

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

   Once started, a DMA stream can be suspended so that the stream hardware configurations
   is kept but the DMA engine stops executing the data transfer. Such a usage is useful,
   for example, for backbuffer/frontbuffer transmission at software update time, in order to
   keep coherency of the data to be transmitted.

   A suspended DMA stream can be:

   * resumed: the DMA stream starts again from its previously suspended state
   * unassigned: the DMA stream is stopped and cleared, and can't be used again while not
     re-assigned

   At return time, the DMA stream is properly suspended, meaning that the syscall waits for
   the DMA engine to confirm the suspend state before returning.

**Example**

   .. code-block:: C
      :linenos:
      :caption: sample DMA stream suspend sequence

      #include <uapi.h>

      if (sys_dma_start_stream(stream_handle) != STATUS_OK) {
         // the channel may be already assigned, unassign first
      }
      // DMA behave in circular mode

      if (sys_dma_suspend_stream(stream_handle) != STATUS_OK) {
         // [...]
      }
      // working on DMA source or destination....
      // resume stream no that SW update is done
      if (sys_dma_resume_stream(stream_handle) != STATUS_OK) {
         // [...]
      }

**Required capability**

   Like all other DMA-related syscalls, this syscall needs the calling task to hold the CAP_DEV_DMA capability.

**Return values**

   * STATUS_INVALID if the handle do not exist or the DMA stream is not currently started
   * STATUS_DENIED if the stream is not owned or the CAP_DEV_DMA is not hold by the task
   * STATUS_OK if the stream has been suspended. The suspend flag check is checked synchronously

**See also**

    `sys_dma_assign_stream` (2), `sys_dma_unassign_stream` (2), `sys_dma_start_stream` (2), `sys_dma_suspend_stream` (2),
    `sys_get_dma_stream_handle` (2)
