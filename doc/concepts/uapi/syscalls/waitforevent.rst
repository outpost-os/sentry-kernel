sys_wait_for_event
""""""""""""""""""

**API definition**:

.. code-block:: rust
   :caption: Rust UAPI for wait_for_event syscall

   mod uapi {
      fn wait_for_event(mask: u8, timeout: i32) -> Status
   }

.. code-block:: c
   :caption: C UAPI for wait_for_event syscall

   typedef enum EventType {
     EVENT_TYPE_NONE = 0,
     EVENT_TYPE_IPC = 1,
     EVENT_TYPE_SIGNAL = 2,
     EVENT_TYPE_IRQ = 4,
     EVENT_TYPE_ALL = 7,
   } EventType;

   enum Status sys_wait_for_event(uint8_t mask, int32_t timeout);

**Usage**:

This syscall is built in order to be a blocking point of the calling thread.
This syscall handles external events blocking reception (IPCs, signals or interrupt).

In order to wait for specific event(s) only, the mask argument is used in order to
filter some specific inputs events using logical OR between waited event(s).

The timeout argument is used to define the temporal behavior:

   * if ``timeout`` is -1, the syscall synchronously return to the job, with STATUS_AGAIN of no
     event is received
   * if ``timeout`` is 0, the job is preempted until an event is received
   * if ``timeout`` is positive, the job waits upto `timeout` ms. In case of timeout reached,
     STATUS_TIMEOUT is returned

In order to help with the timeout flag usage, C macros as been written to hide the field numeric value:

.. code-block:: c
   :caption: wait_for_event timeout helpers

   #define WFE_WAIT_NO      (-1)
   #define WFE_WAIT_FOREVER (0)
   #define WFE_WAIT_UPTO(x) (x)

Any received event is delivered with a TLV basic content in the **svc_exchange** area:

```
[T:u8][L:u8][magic:u16][source:u32][data...]
```

The T field is keeping the enumerate EventMask encoding, in order to identify the
type of received event.

.. note::
    Only one type of event per call is returned, meaning that only EVENT_IPC, EVENT_SIGNAL
    or EVENT_IRQ is used for the T field

The L field always specify the exact data size. This means that:

   * An IPC event L field is equal to the effective received bytes
   * A signal event L field is always equal to 4 (signal value length)
   * An IRQ fevent L field hold one or more IRQ numbers. Each IRQ value being
     encoded on 16 bits values, meaning that the number of received IRQ is equal
     to L/2. In that last case, the IRQ are stored in the chronologically received order

The magic field is used in order to detect invalid exchange content easily, to prevent
invalid data values access from userspace upper layers.

The exchange event is an UAPI types that is defined as the following:

.. code-block:: c
   :caption: wait_for_event helper struct

   typedef struct exchange_event {
       uint8_t type;   /*< event type, as defined in uapi/types.h */
       uint8_t length; /*< event data length, depending on event */
       uint16_t magic; /*< event TLV magic, specific to input event reception */
       uint32_t source; /*< event source (task handle value). 0 means the kernel */
       uint8_t data[]; /*< event data, varies depending on length field */
   } exchange_event_t;

This make the syscall usage easier:

.. code-block:: c
   :caption: Typicall wait_for_event usage

   exchange_event_t * event = NULL;
   status = wait_for_event(EVENT_TYPE_IPC | EVENT_TYPE_SIGNAL, WFE_WAIT_NO);
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


.. note::
   The wait_for_event() API is typically manipulated through the msgrcv() POSIX
   API implemented in libshield

.. warning::
   Not that svc_exhchange area content is ephemeral upto the next syscall. The developper should
   copy its content to a safe area or manipulate it withtout any syscall in the between (including sys_log())
