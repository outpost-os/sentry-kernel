sys_wait_for_event
""""""""""""""""""

.. _wait for event:
.. _event_type:

**API definition**

   .. code-block:: c
      :caption: C UAPI for wait_for_event syscall

      typedef enum EventType {
        EVENT_TYPE_NONE = 0,
        EVENT_TYPE_IPC = 1,
        EVENT_TYPE_SIGNAL = 2,
        EVENT_TYPE_IRQ = 4,
        EVENT_TYPE_DMA = 8,
        EVENT_TYPE_ALL = 0xf,
      } EventType;

      enum Status __sys_wait_for_event(uint8_t mask, int32_t timeout);

**Usage**

   This syscall is designed in order to be a blocking point of the calling thread. Yet,
   it also allows non-blocking mode if needed.

   The goal of this syscall is to wait for various external events such as:

      * IPC
      * signals
      * IRQ
      * DMA

   Returning from this syscall in blocking mode means that an event has been received or
   the blocking timeout has been reached.
   In non-blocking mode, this syscall returns immediately, even if no event has been received.

   The `mask` argument is used in order to filter which event type is waited.

   .. warning::
      Waiting for no event type at all in blocking mode will always reach the timeout or in
      full blocking mode will leave the job de-scheduled for ever.

   When using multiple call to `wait_for_event`, the non-blocking mode should be preferred to
   avoid multiple blocking points in the same thread.

   The `timeout` argument is used to define the temporal behavior.

   the timeout argument the following, canonically defined, values:

   .. code-block:: c
      :caption: wait_for_event timeout helpers

      #define WFE_WAIT_NO      (-1)
      #define WFE_WAIT_FOREVER (0)
      #define WFE_WAIT_UPTO(x) (x)


   * if ``timeout`` is WFE_WAIT_NO, the syscall synchronously return to the job
   * if ``timeout`` is 0, the job is preempted until an event is received
   * if ``timeout`` is positive, the job waits up-to `timeout` milliseconds.

   the `wait_for_event` API only returns a single event type, even if multiple
   heterogeneous events are set in the job input queue. As a consequence, there is
   an event types receiving order that has been defined in the kernel implementation.
   Events type receiving order respects the following:

   1. Signals events
   2. IRQ events
   3. DMA events
   4. IPC events

**Return code**

   * If an event is received, the event data are written in the SVC_EXCHANGE area
     and the syscall returns STATUS_OKAY. In blocking mode, if the job was preempted
     during the syscall execution, the quantum is reset to its declared value.

   * If the declared timeout is reached without receiving any event, the syscall
     returns STATUS_TIMEOUT. The job has its quantum reset to its configured value at
     the time of the syscall returns.

   * If the syscall is in non-blocking mode and no event exists in the job input queue
     at the time of the syscall execution, STATUS_AGAIN is returned. The job can continue
     its execution up-to reaching its quantum.

   * If any of the argument is invalid, the syscall synchronously returns STATUS_INVALID.
     The job can continue its execution up-to reaching its quantum.

**Returned data**

   If the syscall returns `STATUS_OKAY` the kernel always push event in the SVC_EXCHANGE data.

   The data returned in the SVC_EXCHANGE area respects the data encoding defined in
   :ref:`events definition <event header>`. The returned event type is always one of the
   events that have been required in the `mask` argument.

   The magic field is used in order to detect invalid exchange content easily, to prevent
   invalid data values access from userspace upper layers.

   The data field length depend on the received event type. The events type length and content
   are defined in the *About events* chapter of Sentry concepts.

**Example**

   .. code-block:: c
      :caption: Typicall wait_for_event usage

      exchange_event_t * event = NULL;
      status = __sys_wait_for_event(EVENT_TYPE_IPC | EVENT_TYPE_SIGNAL, WFE_WAIT_NO);
      switch (status) {
         case STATUS_OKAY:
            /* an IPC or signal is received */
            event = &_s_svcexchange;
            switch (event->type) {
               case EVENT_TYPE_IPC:
                  /* handle IPC */
                  break;
               case EVENT_TYPE_SIGNAL:
                  /* handle signal */
                  break;
               default:
                  break;
            }
            break;
         case STATUS_AGAIN:
            break;
         default:
            /* others are errors that should be handled */
            break;
      }

   .. warning::
      Note that svc_exhchange area content is ephemeral up-to the next syscall. The developer should
      copy its content to a safe area or manipulate it without any syscall in the between
